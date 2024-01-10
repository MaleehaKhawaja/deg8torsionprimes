//The following code supports 
//the proof of Lemma 4.3.
//The code is a slight modification of Michael Stoll's code
//which can be found at https://www.mathe2.uni-bayreuth.de/stoll/magma/DKSS/DKSS.magma

load "X1_p.m"; // load the curves X_1(p) over F_2

P<x> := PolynomialRing(Rationals());

// Partition of point sets into orbits under Frobenius.
frob := func<pt | Parent(pt)![s^2 : s in Eltseq(pt)]>;

function frob_orbits(pts)
  orbits := [Parent({Rep(pts)})|];
  pts := Set(pts); // pts is an indexed set; turn into a set
  while not IsEmpty(pts) do
    rep := Rep(pts);
    orb := {rep};
    while true do
      rep := frob(rep);
      if rep in orb then break; end if;
      Include(~orb, rep);
    end while;
    Append(~orbits, orb);
    pts diff:= orb;
  end while;
  return orbits;
end function;

// For p = 37, check that all positive-rank simple factors
// of J_1(p) occur in J_0(p).

printf "checking claims on positive-rank simple factors of J_1(p)...\n\n";

for p in [37] do
  assert #[M : M in NewformDecomposition(CuspidalSubspace(ModularSymbols(Gamma1(p),2,1)))
             | IsZero(WindingElementProjection(M))]
           eq #[M : M in NewformDecomposition(CuspidalSubspace(ModularSymbols(Gamma0(p),2,1)))
                  | IsZero(WindingElementProjection(M))];
end for;

// For the further computations, we first set up lists of all elliptic
// curves (up to isomorphism) over the fields F_{2^n}, for n = 1, ..., 7,
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

// Deal with p = 37 and d = 8.

// First show that only one diamond orbit of degree-6 places on X_1(37)
// satisfies the principality criterion and no degree-7 place does.
// We can take any a here, since the only positive-rank component
// of J_1(37) comes from J_0(37) (see below).
printf "Show that only one diamond orbit of places of degree 6\n";
printf "satisfies the critrion of Lemma 8.6 and that no other place\n";
printf "of degree d <= 7 does...\n";
for d := 1 to 5 do
  assert IsEmpty(surviving_places(37, 3, d));
end for;
time surv, places := surviving_places(37, 3, 6); // ~ 20 sec
assert #surv eq 1;
time assert IsEmpty(surviving_places(37, 3, 7)); // ~ 5 sec
time assert IsEmpty(surviving_places(37, 3, 8)); // ~ 0 sec

// Precision bound for q-expansions
prec := 200;

printf "\nNow show that this gives an essentially unique sporadic point\n";
printf "in X_1(37)^(6)(Q) and no non-cuspidal point in X_1(37)^(7)(Q).\n\n";

printf "\nsetting up modular symbols...\n\n";
// Set up modular symbols for Gamma_1(37).
M := ModularSymbols(Gamma1(37), 2, 1);
MS := CuspidalSubspace(M);
g := Dimension(MS); // 40, the genus of X_1(37)
// Get a basis of differentials with integral q-expansions.
qbas := qIntegralBasis(MS, prec);
// Find quadratic relations between them.
printf "constructing canonical model of X_1(37) over F_2...\n\n";
P := PolynomialRing(Integers(), g);
mons2 := MonomialsOfDegree(P, 2);
monsq := [Evaluate(m, qbas) : m in mons2];
mat := Matrix([[Coefficient(s, j) : j in [2..prec]] : s in monsq]);
kermat := KernelMatrix(mat); // takes a few seconds
pols := [&+[kermat[i,j]*mons2[j] : j in [1..#mons2]] : i in [1..Nrows(kermat)]];
// Check that the space of quadrics vanishing on the image
// has the correct dimension.
// Note: binom(g+1, 2) is number of monomials of degree 2,
// the dimension of L(2*canonical) is 3(g-1).
assert #pols eq Binomial(g+1, 2) - 3*(g-1);

// Reduce the model of X_H mod 2.
PF2<[x]> := PolynomialRing(GF(2), g);
pols2 := [PF2!pol : pol in pols];
Pr := ProjectiveSpace(PF2);
X := Curve(Pr, pols2);

printf "find points over F_{2^6}...\n\n";
// We want points over F_{2^6}, so base-change to that field.
X_6 := BaseChange(X, GF(2^6));
// Find all points on X over that field.
time pts6 := &join{Points(Scheme(X_6, X_6.2-a*X_6.1)) : a in GF(2^6)}
              join Points(Scheme(X_6, X_6.1)); // about 5 minutes

// Partition into orbits under Frobenius.
orbits := frob_orbits(pts6);

printf "determine factor of winding quotient...\n\n";
// The only positive-rank component is the first space in the decomposition,
// corresponding to the elliptic curve of conductor 37 and rank 1.
decomp := NewformDecomposition(MS);
assert [Dimension(D) : D in decomp] eq [1,1,2,2,4,6,6,18];
S := &+decomp[[3,5,6,7,8]];
// Verify that the associated abelian variety belongs to the
// winding quotient and all isogeneous abelian varieties
// have odd order torsion.
assert forall{M : M in decomp[2..#decomp] | not(IsZero(WindingElementProjection(M)))};
assert IsOdd(TorsionBound(S, 10));
// Verify that T_{17} has eigenvalue 0 on the positive-rank space
// and has nonzero eigenvalues mod 2 on S
assert IsZero(HeckeOperator(decomp[1], 17));
assert IsOdd(Determinant(IntegralHeckeOperator(S, 17)));

printf "set up projection...\n\n";
// Find the corresponding projection phi: X --> P^{dim A - 1}.
// Get Z-basis of differentials in terms of q-expansions.
qbasS := qIntegralBasis(S, prec);
// Write them as linear combinations on the basis of MS.
matMS := Matrix([[Coefficient(s, j) : j in [1..prec-1]] : s in qbas]);
qbasSinqbas := Matrix([Solution(matMS, Vector([Coefficient(b, j) : j in [1..prec-1]]))
                        : b in qbasS]);
// This gives the linear forms over F_2 realizing the projection phi.
linforms := [&+[qbasSinqbas[i,j]*PF2.j : j in [1..Ncols(qbasSinqbas)]]
                 : i in [1..Nrows(qbasSinqbas)]];

// These are the honest degree 6 points (all of them, not up to the action of Frob).
deg6 := &join[o : o in orbits | #o eq 6]; 

printf "verify criterion for d = 6 ...\n\n";
// In principle, we only need to check the conditions on one of the
// orbits that is the image of an orbit of degree-6 points on X_1(37)
// that survive the principality criterion,
// but it is hard to figure out which one it is.
// So we do it for all representative points we found.
// Evaluate at each point in deg6 to check that not all are zero.
lfeval := [[Evaluate(l, Eltseq(pt)) : l in linforms] : pt in deg6];
assert forall{a : a in lfeval | exists{b : b in a | b ne 0}};
// Check for each point that its coordinates generate a 6-dim'l space over F_2.
mattr := [Transpose(Matrix([Eltseq(b) : b in a])) : a in lfeval];
assert forall{m : m in mattr | Rank(m) eq 6};
printf "successful!\n\n";

printf "verify criterion for d = 7 ...\n\n";
// We check that the criterion is also satisfied for the sum of
// the image of a rational cusp with a divisor of degree 6.
// First find the F_2-rational cusps.
time pts1 := Points(Scheme(X, X.1)) join Points(Scheme(X, X.2))
              join Points(Scheme(X, X.1+X.2)); // ~ 10 sec
assert #pts1 eq 18; // exactly the images of the rational cusps
// Check non-vanishing condition at the cusps
assert forall{pt : pt in pts1
                 | exists{l : l in linforms | Evaluate(l, Eltseq(pt)) ne 0}};
// Generate rows for the cusps
vectors := [Vector(GF(2), [Evaluate(l, Eltseq(pt)) : l in linforms]) : pt in pts1];
// Check the rank condition.
assert forall{m : m in mattr, v in vectors | Rank(Matrix(Append(Rows(m), v))) eq 7};
printf "successful!\n\n";



printf "verify criterion for d = 8 ...\n\n";
// We check that the criterion is also satisfied for the sum of
// the image of two rational cusp with a divisor of degree 6.
// Check non-vanishing condition, first assuming that the 
// two cusps are distinct.

for m in mattr do
	for i in [1..17] do
		p:=pts1[i];
		for j in [(i+1)..18] do
			q:=pts1[j];
			assert Rank(Matrix(Append(Append(Rows(m), Vector(GF(2),[Evaluate(l, Eltseq(p)) : l in linforms])), Vector(GF(2),[Evaluate(l, Eltseq(q)) : l in linforms])))) eq 8;
		end for;
	end for;
end for;

// Next we consider the case where the two rational cusps are equal.
// Applying a diamond operator, we may assume that our cusp is \infty.
// We will use the q-expansions to get the relevant coefficients
// of the Derickx matrix.

R<t>:=PowerSeriesRing(GF(2),500);
W:=PolynomialRing(Integers(),40);
qbas2:=[ (R!Evaluate(W!l,qbas))   : l in linforms];
assert &and[Valuation(f) ge 1 : f in qbas2];
qbas2:=[f div t : f in qbas2];
row1:=Vector(GF(2),[Coefficient(f,0) : f in qbas2]);
row2:=Vector(GF(2),[Coefficient(f,1) : f in qbas2]);
for m in mattr do
	assert Rank(Matrix(Rows(m) cat [row1,row2])) eq 8;
end for;
