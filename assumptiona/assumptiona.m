//The following code supports 
//the claims made in Section 3.
//The code is a slight modification of Michael Stoll's code
//which can be found at https://www.mathe2.uni-bayreuth.de/stoll/magma/DKSS/DKSS.magma

// Kamienny's criterion for X_0(p)

function kamienny0(p, l, d : max_n := 60, max_q := 20)
  // Set up modular symbols for Gamma_0(p)
  M := ModularSymbols(Gamma0(p));
  MS := CuspidalSubspace(M);
  // the winding element as an element of the rational homology
  e := WindingElementProjection(MS);
  S := ModularSymbols(p, 2, -1); // dual to the space of cusp forms
  function t1(n) // apply t_1 to t_0 = T_n
    Tn_MS := HeckeOperator(MS, n);
    Tn_S := IntegralHeckeOperator(S, n);
    pol := CharacteristicPolynomial(Tn_S);
    fpol := Factorization(pol);
    factors := [f : f in fpol | f[2] ge 2 or e*Evaluate(ExactQuotient(pol, f[1]^f[2]), Tn_MS) eq 0];
//     printf "exponents: %o\n", [f[2] : f in fpol];
    return Evaluate(&*[Parent(pol) | f[1]^f[2] : f in factors], Tn_S);
  end function;
  id := IntegralHeckeOperator(S, 1);
  if l eq 2 and p mod 8 eq 1 then
    t2_list := [<q, IntegralHeckeOperator(S, q) - (q+1)*id>
                  : q in PrimesInInterval(3, max_q) | q ne p];
  else
    t2_list := [<1, id>];
  end if;
  // Hecke operators T_1, ..., T_d mod l
  hecke := [ChangeRing(IntegralHeckeOperator(S, j), GF(l)) : j in [1..d]];
  for n := 2 to max_n do
    t1n := t1(n);
    for pair in t2_list do
      t := ChangeRing(t1n*pair[2], GF(l));
      // check linear independence of t*T_j for j = 1,...,d
      if Rank(Matrix([Eltseq(t*T) : T in hecke])) eq d then
        return true, n, pair[1];
      end if;
    end for;
  end for;
  return false, _, _;
end function;

function kamienny0rc(p, l, d : max_n := 60, max_q := 20, ops := [2,3,5,7])
  // Set up modular symbols for Gamma_0(p)
  M := ModularSymbols(Gamma0(p));
  MS := CuspidalSubspace(M);
  // the winding element as an element of the rational homology
  e := WindingElementProjection(MS);
  S := ModularSymbols(p, 2, -1); // dual to the space of cusp forms
  Tnseq_S := [IntegralHeckeOperator(S, n) : n in ops];
  Tnseq_MS := [HeckeOperator(MS, n) : n in ops];
  function t1(cofs) // apply t_1 to t_0 = cofs[1]*T_2 + ... + cofs[4]*T_7
    Tn_MS := &+[cofs[i]*Tnseq_MS[i] : i in [1..#ops]];
    Tn_S := &+[cofs[i]*Tnseq_S[i] : i in [1..#ops]];
    pol := CharacteristicPolynomial(Tn_S);
    fpol := Factorization(pol);
    factors := [f : f in fpol | f[2] ge 2 or e*Evaluate(ExactQuotient(pol, f[1]^f[2]), Tn_MS) eq 0];
//     printf "exponents: %o\n", [f[2] : f in fpol];
    return Evaluate(&*[Parent(pol) | f[1]^f[2] : f in factors], Tn_S);
  end function;
  id := IntegralHeckeOperator(S, 1);
  if l eq 2 and p mod 8 eq 1 then
    t2_list := [<q, IntegralHeckeOperator(S, q) - (q+1)*id>
                  : q in PrimesInInterval(3, max_q) | q ne p];
  else
    t2_list := [<1, id>];
  end if;
  // Hecke operators T_1, ..., T_d mod l
  hecke := [ChangeRing(IntegralHeckeOperator(S, j), GF(l)) : j in [1..d]];
  for n := 1 to max_n do
    cofs := [Random({-1..1}) : i in [1..#ops]];
    t1n := t1(cofs);
    for pair in t2_list do
      t := ChangeRing(t1n*pair[2], GF(l));
      // check linear independence of t*T_j for j = 1,...,d
      if Rank(Matrix([Eltseq(t*T) : T in hecke])) eq d then
        return true, cofs, pair[1];
      end if;
    end for;
  end for;
  return false, _, _;
end function;

// Run the check for all primes in plist.
// Returns the sequence of primes, for which the criterion failed
// and the largest n and q used for those where it was successful.
function check_kam0(plist, l, d)
  max_n := 0; max_q := 0;
  fail := [];
  for p in plist do
    t0 := Cputime();
    flag, n, q := kamienny0(p, l, d);
    t := Cputime(t0);
    if flag then
      max_n := Max(max_n, n);
      max_q := Max(max_q, q);
      if l eq 2 then
        printf "p = %o: success with T_%o and q = %o (%o sec)\n", p, n, q, t;
      else
        printf "p = %o: success with T_%o (%o sec)\n", p, n, t;
      end if;
    else
      Append(~fail, p);
      printf "p = %o: failure (%o sec)\n", p, t;
    end if;
  end for;
  return fail, max_n, max_q;
end function;

check_kam0(PrimesInInterval(29,1000), 2, 8); //We executed this function in several parallel computations for all primes 23<p<6724.
