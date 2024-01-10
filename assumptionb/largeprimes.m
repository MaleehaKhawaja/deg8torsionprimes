//We verify that p does not lie in S(8)
// for p = 113, 127, 131, 137, 139, 241, 257

print "For p in [113,127,131,137,139,241,257], we check\\ 
that the positive-rank factors of J1(p) already occur\\ 
in J0(p).";

time for p in [113, 127, 131, 137, 139, 241, 257] do
        print p;
        assert #[M : M in NewformDecomposition(CuspidalSubspace(ModularSymbols(Gamma1(p),2,1)))
             | IsZero(WindingElementProjection(M))]
           eq #[M : M in NewformDecomposition(CuspidalSubspace(ModularSymbols(Gamma0(p),2,1)))
                  | IsZero(WindingElementProjection(M))];
end for;

print 'Success!';

//For each p, we find a primitive root 
//modulo p

for p in [113, 127, 137, 139, 257]
    do F:=GF(p);
    a:=F!3;
    assert IsPrimitive(a);
end for;

F:=GF(131);
a:=F!2;
assert IsPrimitive(a);

F:=GF(241);
a:=F!7;
assert IsPrimitive(a);

//We check that the bound given 
//in Proposition 7.1 holds.

for p in [113, 127, 137, 139, 257]
    do assert 8 le (325*(p^2-1))/(2^16*7);
end for;

assert 8 le (325*(241^2-1))/(2^16*8);
assert 8 le (325*(131^2-1))/(2^16*8);