load "X1p.m"; //This loads the curves X1(p) over F_2

//The following code supports 
//the proof of Lemma 2.3. 
//The code is a slight modification of Michael Stoll's code
//which can be found at https://www.mathe2.uni-bayreuth.de/stoll/magma/DKSS/DKSS.magma

// p = 29
printf "p = 29\n";
printf "------\n\n";
p := 29;
X := X1p_models[p];
assert Genus(X) eq 22; // check that model reduces well
plc := Places(X, 1);
assert #plc eq ExactQuotient(p-1, 2); // sanity check
printf "setting up Picard group...\n";
time Cl, CltoDiv, DivtoCl := ClassGroup(X); // takes a bit more than one minute
bpt := DivtoCl(Divisor(plc[1]));
printf "verifying first claim...\n";
G := sub<Cl | [DivtoCl(Divisor(plc[i])) - bpt : i in [2..#plc]]>;
assert Valuation(#G, 2) eq 6;
// see Table 1 in [CES03]; note that the entry there must be divided by 2^6

// Check assumption (b)

printf "Verifying assumption b) holds for p=29";
plc8 := Places(X, 8);
// Check that the prime divisors of degree 8 do not map into G.
assert forall{pl : pl in plc8 | DivtoCl(Divisor(pl)) - 8*bpt notin G};

printf "successful!\n\n";
