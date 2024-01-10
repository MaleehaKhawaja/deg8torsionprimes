//The following code supports 
//the claims made in Section 3.
//The code is a slight modification of Michael Stoll's code
//which can be found at https://www.mathe2.uni-bayreuth.de/stoll/magma/DKSS/DKSS.magma

// Version for X_H with speed-up.

function kamiennyH(p, d, h : max_n := 60, max_q := 20)
  // h represents a generator of H.
  // Set up modular symbols for Gamma_H.
  M := ModularSymbolsH(p, [h], 2, 0);
  MS := CuspidalSubspace(M);
  e := WindingElementProjection(MS);
  S := ModularSymbolsH(p, [h], 2, -1); // dual to the space of cusp forms
  function diamond(q)
    // diamond operator <q> for q prime
    op := IntegralHeckeOperator(S, q)^2 - IntegralHeckeOperator(S, q^2);
    return ChangeRing(1/q*ChangeRing(op, Rationals()), Integers());
  end function;
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
  // We could try to figure out whether the rational torsion subgroup
  // on the winding quotient has odd order, in which case
  // we can set t2_list := [<1, id>];
  t2_list := [<q, IntegralHeckeOperator(S, q) - q*id - diamond(q)>
                : q in PrimesInInterval(3, max_q) | q ne p];
  // Hecke operators T_1, ..., T_d mod 2
  hecke := [ChangeRing(IntegralHeckeOperator(S, j), GF(2)) : j in [1..d]];
  r := 1; repeat r := NextPrime(r); until Order(GF(p)!r) eq p-1;
  // r is prime and generates the quotient (Z/pZ)^*/+-H
  dia := ChangeRing(diamond(r), GF(2));
  U, fromU := UnitGroup(GF(p));
  index := Index(U, sub<U | [(GF(p)!-1) @@ fromU, (GF(p)!h) @@ fromU]>);
  dias := [dia^j : j in [0..index-1]];
  d2 := d div 2;
  for n := 2 to max_n do
    vprintf User1: "Working with t_0 = T_%o\n", n;
    t1n := t1(n);
    for pair in t2_list do
      vprintf User1: "  Using second factor with q = %o\n", pair[1];
      t := ChangeRing(t1n*pair[2], GF(2));
      products := [[tt*T : T in hecke[1..j eq 1 select d else d2]]
                     where tt := t*dias[j] : j in [1..#dias]];
      mat := Matrix([Eltseq(op) : op in &cat products]);
      ker := Kernel(mat);
      vprintf User1: "    dim(ker) = %o\n", Dimension(ker);
      // Use linear codes machinery to enumerate short relations.
      code := LinearCode(ker);
      dist := PartialWeightDistribution(code, d);
      num := &+[Integers() | e[2] : e in dist[2..#dist]]; // number of nonzero words
      // Skip if number is too large
      if num gt 10000 then
        vprintf User1: "    too many short relations\n";
        continue pair; // try next pair of operators
      else
        rels := &join{Words(code, l) : l in [1..d]};
      end if;
      for rel in rels do
        cofs := Eltseq(rel);
        // Check if relation is of the correct (i.e., forbidden) form
        parts := [cofs[1..d]] cat [cofs[d+j*d2+1..d+(j+1)*d2] : j in [0..index-2]];
        // The sum of the (1-based) position numbers of the last "1"
        // in each part must be <= d.
        positions := [last_one(part) : part in parts]
          where last_one := function(seq)
                              for i := #seq to 1 by -1 do
                                if seq[i] eq GF(2)!1 then return i; end if;
                              end for;
                              return 0;
                            end function;
        if &+positions le d then
          // offending relation found
          vprintf User1: "    linear depenence found!\n";
          continue pair; // try next pair of operators
        end if;
      end for;
      // If we get here, no offending relations were found ==> success.
      return true, n, pair[1];
    end for;
  end for;
  return false, _, _;
end function;

// Determine a representative of a generator of H from H's index.
function genH(p, index)
  assert IsDivisibleBy(p-1, 2*index);
  r := PrimitiveRoot(p);
  return Integers()!((GF(p)!r)^index);
end function;

function kamienny(p, d)
  // Try all possible H's, starting with smallest index > 1
  // (we assume we already did kamienny0).
  t0 := Cputime();
  indices := Divisors(ExactQuotient(p-1, 2));
  for ind in indices[2..#indices] do
    flag, n, q := kamiennyH(p, d, genH(p, ind));
    if flag then
      t := Cputime(t0);
      printf "p = %o: success with index(H) = %o, T_%o and q = %o (%o sec)\n", p, ind, n, q, t;
      return true, ind, n, q;
    end if;
  end for;
  return false, _, _, _;
end function;

lst:=PrimesInInterval(31, 137) cat [139, 151, 157, 191, 223]; //29 verified separately in Lemma 2.3

time for p in lst 
  do assert kamienny(p, 8);
end for;
