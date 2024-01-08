//The following code supports 
//the proof of Lemma 2.3. 
//The code is a slight modification of Michael Stoll's code
//which can be found at https://www.mathe2.uni-bayreuth.de/stoll/magma/DKSS/DKSS.magma

// For p = 31, 41, 47, 59, 71, check that all positive-rank simple factors
// of J_1(p) occur in J_0(p).

printf "checking claims on positive-rank simple factors of J_1(p)...\n\n";

for p in [31, 41, 47, 59, 71] do
  assert #[M : M in NewformDecomposition(CuspidalSubspace(ModularSymbols(Gamma1(p),2,1)))
             | IsZero(WindingElementProjection(M))]
           eq #[M : M in NewformDecomposition(CuspidalSubspace(ModularSymbols(Gamma0(p),2,1)))
                  | IsZero(WindingElementProjection(M))];
end for;

// For the further computations, we first set up lists of all elliptic
// curves (up to isomorphism) over the fields F_{2^n}, for n = 1, ..., 8,
// restricting to one representative of each orbit of Forbenius.

function F2n_mod_frob(n)
  F := GF(2, n);
  set := Set(F);
  result := {F| };
  while not IsEmpty(set) do
    a := Rep(set);
    Include(~result, a);
    b := a;
    repeat
      Exclude(~set, b);
      b := b^2;
    until b eq a;
  end while;
  return result;
end function;

curves := [[<E, #E> : E in &cat[Twists(EllipticCurveFromjInvariant(j)) : j in F2n_mod_frob(n)]]
             : n in [1..8]];

// We translate between non-cuspidal points on X_1(p) over F_2
// and pairs (E, P) consisting of an elliptic curve E over F = F_{2^n}
// and a point P in E(F) of exact order p by representing (E, P) by
// its Tate parameters, i.e., (b, c) in F^2 such that (E, P) is isomorphic to
//  (Y^2 + (1-c) XY - b Y = X^3 - b X^2,  (0, 0)) .
// The coordinates (x, y) of the models of X_1(p) we use
// are related to (b, c) via
//   r = b/c,  s = c^2/(b-c);   b = rs(r-1),  c = s(r-1)
//   x = (s-r)/(rs-2r+1),  y = (rs-2r+1)/(s^2-s-r+1);
//   r = (x^2y-xy+y-1)/(x(xy-1)),  s = (xy-y+1)/(xy).

function EP_to_xy(E, P)
  // E in elliptic curve over some field F, P in E(F) not of order 1, 2, 3.
  // Returns (x, y) in F^2 derived from Tate parameters (b, c) as above.

  // First transform to Tate form.
  assert P[3] eq 1; // P is not the origin
  // extract affine coordinates of P
  x0 := P[1];
  y0 := P[2];
  // and the coefficients of E
  a1, a2, a3, a4, a6 := Explode(aInvariants(E));
  // shift coordinates to put P at (0, 0)
  a1, a2, a3, a4 := Explode([a1, a2 + 3*x0, a3 + a1*x0 + 2*y0, a4 + 2*x0*a2 - a1*y0 + 3*x0^2]);
  // make y = 0 the tangent line at (0, 0)
  lambda := a4/a3; // slope of tangent
  a1, a2, a3 := Explode([a1 + 2*lambda, a2 - lambda*a1 - lambda^2, a3]);
  // scale x and y to make a2 = a3 --> get b = -a2, c = 1 - a1
  u := a2/a3; // scaling factor
  b := -a2*u^2;
  c := 1 - a1*u;
  // compute x and y from b and c
  r := b/c;
  s := c^2/(b - c);
  t := r*s - 2*r + 1;
  x := (s - r)/t;
  y := t/(s^2 - s - r + 1);
  return x, y;
end function;

function xy_to_EP(x, y)
  // x, y in a field F.
  // Returns E in Tate form corresponding to (x, y) (with P = E![0,0]).

  // compute b and c from x and y
  xy := x*y;
  t := xy - y + 1;
  s := t/xy;
  r := (x*xy - t)/(x*(xy - 1));
  c := s*(r - 1);
  b := r*c;
  // construct Tate curve
  return EllipticCurve([1-c, -b, -b, 0, 0]);
end function;

function place_from_point(pt)
  // pt is a point on a curve over an extension of the base field.
  // Returns the unique place determined by pt.
  plcs := Places(pt);
  assert #plcs eq 1;
  return plcs[1];
end function;

// Compute the effect of a diamond operator <a> on (x, y).
function diamondop(a, x, y)
  E := xy_to_EP(x, y);
  return EP_to_xy(E, a*E![0,0]);
end function;

// Now the effect on a divisor.
function diamondop_div(a, D)
  // split divisor into places with multiplicities
  plcs, mults := Support(D);
  X := Curve(D);
  // apply <a> to a point of each place and turn back into places
  pts := [* Eltseq(RepresentativePoint(plc)) : plc in plcs *];
  assert forall{1 : s in pts | s[3] eq 1}; // all affine points
  pts := [X(Universe(s))![x,y,1] where x, y := diamondop(a, s[1], s[2]) : s in pts];
  newplcs := [place_from_point(pt) : pt in pts];
  assert forall{i : i in [1..#plcs] | Degree(plcs[i]) eq Degree(newplcs[i])}; // sanity check
  return &+[Parent(D)| mults[i]*newplcs[i] : i in [1..#plcs]];
end function;

// Given x, y, return the sequence of four pairs <x', y'>
// corresponding to 3-isogenous curves with the image of P.
function T3(x, y)
  E := xy_to_EP(x, y);
  pol := DivisionPolynomial(E, 3);
  // each linear factor corresponds to one isogeny
  F := SplittingField(pol);
  fact := Factorization(ChangeRing(pol, F));
  lins := &cat[[e[1] : i in [1..e[2]]] : e in fact];
  EF := BaseChange(E, F);
  isogs := [<EE, isog> where EE, isog := IsogenyFromKernel(EF, lin) : lin in lins];
  return [<x1, y1> where x1, y1 := EP_to_xy(e[1], e[2](EF![0,0])) : e in isogs];
end function;

// The effect of T_3 on a divisor.
function T3_div(D)
  // split divisor into places with multiplicities
  plcs, mults := Support(D);
  X := Curve(D);
  // collect result
  result := Parent(D)!0;
  // apply T3 to a representative point of each place
  for i := 1 to #plcs do
    pt := Eltseq(RepresentativePoint(plcs[i]));
    assert pt[3] eq 1; // affine point
    T3pt := SequenceToMultiset(T3(pt[1], pt[2]));
    F := Universe(Eltseq(pt)); // field of definition
    // find Frobenius orbits over F
    orbs := [];
    while not IsEmpty(T3pt) do
      t := Rep(T3pt);
      orb := {Universe(T3pt)| };
      t1 := t;
      repeat
        Exclude(~T3pt, t1);
        Include(~orb, t1);
        t1 := <t1[1]^#F, t1[2]^#F>;
      until t1 eq t;
      Append(~orbs, orb);
    end while;
    Dpt := Parent(D)!0;
    for orb in orbs do
      tpt := Rep(orb); tpt := [tpt[1], tpt[2], 1];
      plc := place_from_point(X(Universe(tpt))!tpt);
      Dpt +:= ExactQuotient(Degree(F)*#orb, Degree(plc))*plc;
    end for;
    assert Degree(Dpt) eq 4*Degree(plcs[i]); // sanity check
    result +:= mults[i]*Dpt;
  end for;
  return result;
end function;

// For a prime p, return a sequence of non-cuspidal places D of degree d,
// modulo the action of the diamond operators, such that
// t(D) = (T_3 - 3 <3> - 1) (<a> - 1) (D) is a principal divisor on X_1(p)/F_2.

function surviving_places(p, a, d)
  printf "\nsurviving_places(%o, %o, %o):\n", p, a, d;
  // get X_1(p) over F_2
  X := X1p_models[p];
  F := GF(2, d);
  // get a list of all elliptic curves over F_{2^d} with a point of order p
  Es := [e[1] : e in curves[d] | IsDivisibleBy(e[2], p)];
  printf "  there %o %o elliptic curve%o (mod Frob) with a point of order %o\n",
         #Es eq 1 select "is" else "are", #Es, #Es eq 1 select "" else "s", p;
  // take a point of order p and turn the curves into points on X
  // (since the diamond operators permute the pairs (E, P), with P a point
  //  of order p on E over F, transitively, we get a set of representatives
  //  modulo the action of the diamond operators in this way)
  points := [X(F)| ];
  for E in Es do
    G, mG := AbelianGroup(E);
    m := #OrderedGenerators(G);
    assert IsDivisibleBy(Invariants(G)[m], p);
    pt := mG(ExactQuotient(#G, p)*G.m);
    Append(~points, X(F)![x,y] where x, y := EP_to_xy(E, pt));
  end for;
  // convert into places
  places := [Places(X)| place_from_point(pt) : pt in points];
  printf "  giving %o place%o on X_1(%o)\n", #places, #places eq 1 select "" else "s", p;
  // now, for every place, compute t(D) and check whether this is principal
  result := [Universe(places)| ];
  for plc in places do
    D := diamondop_div(a, 1*plc) - plc;
    D := T3_div(D) - 3*diamondop_div(3, D) - D;
    printf "  testing divisor for being principal...\n";
    time flag := IsPrincipal(D);
    printf "    --> %o\n", flag;
    if flag then Append(~result, plc); end if;
  end for;
  printf "  %o place%o survive%o.\n", #result,
         #result eq 1 select "" else "s", #result eq 1 select "s" else "";
  return result, places;
end function;

// Check that no places of degree <= 8 survive for p = 31, 41, 47, 59, 71
// and a suitable a.

// We use a = 3 in all cases. This makes the degrees of the positive
// and negative parts of the resulting divisors somewhat smaller.

printf "\np = 31 (takes about 4.5 seconds): ";
a := 3;
time
for d := 1 to 8 do
  assert IsEmpty(surviving_places(31, a, d));
end for; 
printf "OK!\n";

printf "\np = 41 (takes about 1 minute): ";
a := 3; 
time
for d := 1 to 8 do
  assert IsEmpty(surviving_places(41, a, d));
end for; // 
printf "OK!\n";

printf "\np = 47 (takes about 4.5 minutes): ";
a := 3;
time
for d := 1 to 8 do
  assert IsEmpty(surviving_places(47, a, d));
end for; 
printf "OK!\n";

printf "\np = 59 (takes about 1 hour): ";
a := 3;
time
for d := 1 to 8 do
  assert IsEmpty(surviving_places(59, a, d));
end for; 
printf "OK!\n";

printf "\np = 71 (takes about 7 hours): ";
a := 3;
time
for d := 1 to 8 do
  assert IsEmpty(surviving_places(71, a, d));
end for; 
printf "OK!\n";
