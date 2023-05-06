// Definition of the type for (general) Quandles
declare type Qndl;

// Definition of the attributes of a Quandle
declare attributes Qndl: Set, Operation, _NumberingMap, _NumberingMapInverse;

intrinsic internal_QuandleMatrix(T :: Qndl) -> SeqEnum[SeqEnum[RngIntElt]]
{ It should not be used by an external user : It generates the internal quandle matrix of the (potential) Quandle T }
	return [ [T`_NumberingMap(T`Operation(<x,y>)) : y in T`Set ]: x in T`Set ];
end intrinsic;

intrinsic internal_NumberingMap(~X :: Qndl) 
{ It defines the numbering map for the quandle X }
	try
		G_NumberingMap := [];
		G_NumberingMapInverse := [];
		Co_Domain := [];
		for index := 1 to  #X`Set do
			Append(~G_NumberingMap, <X`Set[index], index>);
			Append(~G_NumberingMapInverse, <index, X`Set[index]>);
			Append(~Co_Domain, index);
		end for; 

		X`_NumberingMap := map< X`Set -> Co_Domain | G_NumberingMap >;
		X`_NumberingMapInverse := map< Co_Domain -> X`Set | G_NumberingMapInverse >;
	catch DefinitionError
        error "Something went wrong in the definition of the numbering map."; 
    end try;
end intrinsic;

intrinsic internal_checkDiagonal(M :: SeqEnum[SeqEnum[RngIntElt]], uSet :: SetIndx[RngIntElt]) -> BoolElt
{ It should not be used by an external user : It checks whether the table/matrix meets the first requirement of a quandle(for all x in S, x * x = x) }
	
	for index := 1 to (#M) do
		require #M[index] eq #M : "This is not a square sequence of sequences.";
		if M[index,index] ne uSet[index] then 
			return false;
		end if;	
	end for;

	return true;

end intrinsic;

intrinsic internal_checkRows(M :: SeqEnum[SeqEnum[RngIntElt]], uSet :: SetIndx[RngIntElt]) -> BoolElt
{ It should not be used by an external user : It checks whether the table/matrix meets the second requirement(the map px : S -> S    y :-> x * y is a bijection) }
	
	uSet_ := Setseq(uSet); 
	for row := 1 to (#M) do 
		if not (IsSubsequence(uSet_, M[row]: Kind := "Setwise")) then 
			return false;
		end if;
	end for;

	return true;

end intrinsic;

intrinsic internal_checkDistributivity(M :: SeqEnum[SeqEnum[RngIntElt]], uSet :: SetIndx[RngIntElt]) -> BoolElt
{ It should not be used by an external user : It checks whether the table/matrix meets the third requirement(For all elements x, y, z in S: x * (y * z) = (x * y) * (x * z)) }
	expected := uSet eq {@ x : x in [1..#M] @};
	
	if not expected then 
		NMapGraph := [];
		Codomain_ := [];
		for index := 1 to #uSet do
			Append(~NMapGraph, <uSet[index], index>);
			Append(~Codomain_, index);
		end for;
		NMap := map< uSet -> Codomain_ | NMapGraph >;
	end if;
	for x := 1 to (#M) do    
		for y := 1 to (#M) do
			for z := 1 to (#M) do
				
				if expected then 
					if (M[x, M[y, z]] ne M[M[x, y], M[x, z]]) then
						return false;
					end if;
				else 
					if (NMap(M[x, NMap(M[y, z])]) ne NMap(M[NMap(M[x, y]), NMap(M[x, z])])) then
						return false;
					end if;
				end if;


			end for;        
		end for;                
	end for;

	return true;
end intrinsic;

intrinsic internal_isRack(M :: SeqEnum[SeqEnum[RngIntElt]], uSet :: SetIndx[RngIntElt]) -> BoolElt
{ It should not be used by an external user : It checks whether the sequence of sequences M represents a Rack with underlying set uSet }

	axiom2 := internal_checkRows(M, uSet);
	axiom3 := internal_checkDistributivity(M, uSet);

    require axiom2 : "Axiom 2 (Left translations must be bijective) does not hold.";
    require axiom3 : "Axiom 3 (Left distributivity) does not hold.";
                       
	return axiom2 and axiom3;
end intrinsic;

intrinsic internal_isQuandle(Q :: Qndl) -> BoolElt
{ It should not be used by an external user : It checks whether Q is actually a quandle }

	M := internal_QuandleMatrix(Q);
	uSet := Codomain(Q`_NumberingMap);
	if ExtendedType(uSet) eq SetEnum[RngIntElt] then 
		uSet := SetToIndexedSet(uSet);
	end if;

	if ExtendedType(uSet) eq SeqEnum[RngIntElt] then 
		uSet := {@ x : x in uSet @};
	end if;


	axiom1 := internal_checkDiagonal(M, uSet);
	require axiom1 : "Axiom 1 (Idemptotency) does not hold.";
	axiom23 :=  internal_isRack(M, uSet);

	return axiom1 and axiom23;
end intrinsic;

intrinsic internal_AutomorphismGroup(M :: SeqEnum[SeqEnum[RngIntElt]]) -> GrpPerm
{ It should not be used by an external user : Finds the inner automorphism group of the quandle represented by the integral quandle matrix M }

	S_X := Sym(#M);

	permutations := Normaliser(S_X,internal_Inn(M));
	generators := [];

	L := map< M[1] -> S_X | x :-> S_X ! M[x]> ;

	for permutation in permutations do
		admissible := true;
		for x in M[1] do
			if (permutation^-1 * L(x) * permutation) ne L(x^permutation) then 
				admissible := false;
				break;
			end if;
		end for;
		if admissible then 
			Append(~generators, permutation);
		end if;
	end for;
	
	return sub< S_X | generators >;
end intrinsic;

intrinsic internal_Inn(M :: SeqEnum[SeqEnum[RngIntElt]]) -> GrpPerm
{ It should not be used by an external user : Finds the inner automorphism group of the quandle represented by the integral quandle matrix M }
	S_X := Sym(#M);
	ChangeUniverse(~M, S_X);
	
	return sub< S_X | M >;
end intrinsic;

intrinsic internal_Generators(M :: SeqEnum[SeqEnum[RngIntElt]]) -> SetEnum[RngIntElt]
{ It should not be used by an external user : Finds a set of generators for the quandle represented by the integral quandle matrix M }
	
	
	subuniverse := { 1 };
    generators := [ 1 ];
    uSet := [1..#M];
	largest := { 1 };
	generators_tmp := [ 1 ];
	potential := [2..#M];
	while #subuniverse ne #M do

		while not IsEmpty(potential) do
			element := potential[1];
			subuniverse_new := internal_Subquandle(M, uSet, subuniverse, element);
			
			if #subuniverse_new gt #largest then 
				largest := subuniverse_new;
				generators_tmp := generators;
				Append(~generators_tmp, element);
				if #subuniverse_new eq #M then 
					return Seqset(generators_tmp);
				end if;
			end if;
			Remove(~potential, 1);
			potential := [ x : x in potential | x notin subuniverse_new ];
		end while;

		subuniverse := largest;
		generators := generators_tmp;
		potential := [ x : x in M[1] | x notin subuniverse ];
    end while;

    return Seqset(generators);
end intrinsic;

intrinsic internal_Subquandle(F :: SeqEnum[SeqEnum[RngIntElt]], uSet :: SeqEnum[RngIntElt], Elements :: SeqEnum[RngIntElt], Element :: RngIntElt) -> SeqEnum[RngIntElt]
{ It should not be used by an external user : Computes Sg(Elements U Set(Element)). Elements is expected to be a closed set within the quandle with underlying set uSet represented by the integral quandle matrix F }
    
    lookupTable := [ x in Elements : x in uSet ];
    
    lookupTable[ Element ] := true;

    toAdd := [ Element ];
    
    

    while not IsEmpty(toAdd) do
        current := toAdd[1];
        Remove(~toAdd, 1);

        for x in Elements do 

            result := F[x,current];
            if not lookupTable[result] then 
                Append(~toAdd, result);
                lookupTable[result] := true;
            end if;
        
            result := F[current, x];
            if not lookupTable[result] then 
                Append(~toAdd, result);
                lookupTable[result] := true;
            end if;

        end for;

        Include(~Elements, current);

        if (#Elements + #toAdd) eq #F then 
            return F[1];
        end if;

    end while;
    
    return Elements;
end intrinsic;

intrinsic internal_Subquandle(F :: SeqEnum[SeqEnum[RngIntElt]], uSet :: SeqEnum[RngIntElt], Elements :: SetEnum[RngIntElt], Element :: RngIntElt) -> SetEnum[RngIntElt]
{ It should not be used by an external user : Computes Sg(Elements U Set(Element)). Elements is expected to be a closed set within the quandle with underlying set uSet represented by the integral quandle matrix F }
    return Seqset(internal_Subquandle(F, uSet, Setseq(Elements), Element));
end intrinsic;

intrinsic internal_SubquandleSet(M :: SeqEnum[SeqEnum[RngIntElt]], Elements :: SeqEnum[RngIntElt]) -> SeqEnum[RngIntElt]
{ It should not be used by an external user : It computes the the closed set generated by Elements within the quandle represented by the integral quandle matrix M}

	if #Elements le 1 then 
		return Elements;
	end if;

	uSet := [1..#M];

	generated := [ Elements[1] ];
	for index := 2 to #Elements do
		generated := internal_Subquandle(M, uSet, generated, Elements[index]);
	end for;
	return generated;
end intrinsic;

intrinsic internal_Subquandles(F :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SetEnum[RngIntElt]]
{ It should not be used by an external user : Returns all the subquandles of quandle represented by the integral quandle matrix F }
    
    
    subAs := [ ];
    subAsLookup := [ ];
    for x in F[1] do
		subAlgebra := { x };
		Append(~subAs, subAlgebra);
        hash := Hash(subAlgebra);
		if not IsDefined(subAsLookup, hash) then 
			subAsLookup[hash] := [ subAlgebra ];
		else
			Append(~subAsLookup[hash], subAlgebra);
		end if;
    end for;
    
    i := 1;
	uSet := [1..#F];

    while i le #subAs do
        current := subAs[i];
        for element in [ x : x in uSet | x notin current ] do 
            if (#current lt #uSet) then 
                new := internal_Subquandle(F, uSet, current, element);
                if not IsDefined(subAsLookup, hash) then 
					subAsLookup[hash] := [ new ];
					Append(~subAs, new);
				else
					if new notin subAsLookup[hash] then 
						Append(~subAsLookup[hash], new);
						Append(~subAs, new);
					end if;
				end if;
            end if;
        end for;
        i := i + 1;
    end while;

    return subAs;
    
end intrinsic;

intrinsic internal_Monomorphism(A :: SeqEnum[SeqEnum[RngIntElt]], B :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[RngIntElt]
{ It should not be used by an external user : Returns, if one exists, a monomorphism from the quandle represented by the integral quandle matrix A to the quandle represented by the integral quandle matrix B }

    if #A gt #B then 
        return [];
    end if;

    genA := internal_Generators(A);
	homomorphism := [[ 0 : x in A ], []];

	return internal_utility_Monomorphism(A, B, genA, homomorphism);
end intrinsic;

intrinsic internal_NewMonomorphism(A :: SeqEnum[SeqEnum[RngIntElt]], B :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[RngIntElt]
{ It should not be used by an external user : Returns, if one exists, a monomorphism from the quandle represented by the integral quandle matrix A to the quandle represented by the integral quandle matrix B }

    if #A gt #B then
        return [];
    end if;

    genA := internal_Generators(A);

    invImages := internal_Invariants(B);

    Images := [];

    for generator in genA do
        invs := internal_ElementInvariants(A,generator);
        for block in invImages do
            if (&and [invs[i] le block[2][i] : i in [1..5]]) then
                Images[generator] := block[1];
                break;
            end if;
        end for;
    end for;
	homomorphism := [[ 0 : x in A ], []];

	//BLOCK
		print(genA);
	ret := internal_utility_NewMonomorphism(A, B, genA, homomorphism, Images);
// 	if (ret eq []) then
// 		print(genA);
// 		print(Images);
// 	end if;
	//BLOCK
	return ret;
end intrinsic;

intrinsic internal_utility_NewMonomorphism(A :: SeqEnum[SeqEnum[RngIntElt]], B :: SeqEnum[SeqEnum[RngIntElt]], Generators :: SetEnum[RngIntElt], Homomorphism :: SeqEnum[SeqEnum[RngIntElt]], Images :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[RngIntElt]
{ It should not be used by an external user : It should only be used by internal_Monomorphism. It recursively expands a map from the quandle represented by the integral quandle matrix A to the quandle represented by the integral quandle matrix B }

    if IsEmpty(Generators) then
		for x,y in Homomorphism[2] do
			z := A[x,y];
			Hx := Homomorphism[1][x];
			Hy := Homomorphism[1][y];
			Hz := Homomorphism[1][z];
			HxHy := B[Hx, Hy];
			if (Hz eq 0) then
				Homomorphism[1][z] := HxHy;
				Append(~Homomorphism[2], z);
			end if;
		end for;
		if (0 in Homomorphism[1]) then
			return internal_utility_NewMonomorphism(A, B, Generators, Homomorphism, Images);
		else
			return Homomorphism[1];
		end if;
	end if;

	x := 0;
	ExtractRep(~Generators, ~x);
	Images_x := [ y : y in Images[x] | x notin Homomorphism[1] ];


	for y in Images_x do
		HomomorphismExpanded := Homomorphism;
		HomomorphismExpanded[1][x] := y;
		Append(~HomomorphismExpanded[2], x);
		mapping := internal_utility_NewMonomorphism(A, B, Generators, HomomorphismExpanded, Images);
		if mapping ne [] then
			return mapping;
		end if;

	end for;

	return [];

end intrinsic;

intrinsic internal_utility_Monomorphism(A :: SeqEnum[SeqEnum[RngIntElt]], B :: SeqEnum[SeqEnum[RngIntElt]], Generators :: SetEnum[RngIntElt], Homomorphism :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[RngIntElt]
{ It should not be used by an external user : It should only be used by internal_Monomorphism. It recursively expands a map from the quandle represented by the integral quandle matrix A to the quandle represented by the integral quandle matrix B }

    if IsEmpty(Generators) then 

		new := {* x : x in Homomorphism[2] *};
		old := { };
		lookupTable := [ x in Homomorphism[1] : x in [1..#B] ];

		Pairs := [];

		while not IsEmpty(new) do
			for x,y in new do
				Append(~Pairs, <x,y>);
			end for;

			for x in old do
				for y in new do
					Append(~Pairs, <x,y>);
					Append(~Pairs, <y,x>);
				end for;
			end for;

			results := {* *};

			for pair in Pairs do
				x := pair[1];
				y := pair[2];
				z := A[x,y];
				Hx := Homomorphism[1][x];
				Hy := Homomorphism[1][y];
				Hz := Homomorphism[1][z];
				HxHy := B[Hx, Hy];
				if (Hz eq 0) and (not lookupTable[HxHy]) then
					Homomorphism[1][z] := HxHy;
					Append(~Homomorphism[2], z);
					Include(~results, z);
					lookupTable[HxHy] := true;
				else 
					if Hz ne HxHy then 
						return [];
					end if;
				end if;
			end for;
			old := old join new;
			new := results;

		end while;

		return Homomorphism[1];
	end if;


	x := 0;
	ExtractRep(~Generators, ~x);

	Images := [ x : x in B[1] | x notin Homomorphism[1] ];

	for y in Images do
		HomomorphismExpanded := Homomorphism;
		HomomorphismExpanded[1][x] := y;
		Append(~HomomorphismExpanded[2], x);
		mapping := internal_utility_Monomorphism(A, B, Generators, HomomorphismExpanded);
		if mapping ne [] then 
			return mapping;
		end if;

	end for;

	return [];

end intrinsic;

intrinsic internal_Congruences(Q :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SetIndx[SetEnum[RngIntElt]]]
{ It should not be used by an external user : Returns all the congruences of the quandle represented by the integral quandle matrix Q }
    if #Q eq 1 then 
        return [ {@ { 1 } @} ];
    end if;
	InnQ := internal_Inn(Q);
	
	S_X := Sym(#Q);
	
	if IsTransitive(InnQ) then 
		L := map< Q[1] -> S_X | x :-> S_X ! Q[x]>;

		congruences := [ {@ { x : x in Q[1] } @} ];
	    
		blocks := AllPartitions(InnQ);

		a0 := 1;
		for initialBlock in blocks do
			admissible := true;
			expanded_blocks := {@ expansion : expansion in initialBlock^InnQ @};
			A := {L(b)*L(a0)^-1 : b in initialBlock};
			for block in expanded_blocks do
				rep := Rep(block);
				for a in A do
					if rep^a notin block then 
						admissible := false;
						break block;
					end if;
				end for;
			end for;
			if admissible then 
				Append(~congruences, expanded_blocks);
			end if;
		end for;
	else 
		congruences := [ internal_DecodePartition(x) : x in internal_CongruencesDisconnected(internal_UnarifyOperation(Q)) ];
	end if;
	
	Append(~congruences, {@ {x} : x in Q[1] @});
	
	return congruences; 
	
end intrinsic;

intrinsic internal_DecodePartition(pi :: SeqEnum[RngIntElt]) -> SetIndx[SetEnum[RngIntElt]]
{ It decodes a partition pi encoded as explained in CRP1 }

	partition := [ pi[x] lt 0 select { x } else { } : x in [1..#pi] ];
	for index := 1 to #pi do
		if pi[index] lt 0 then 
			Include(~partition, { index });
		else 
			Include(~partition[pi[index]], index);
		end if;
	end for;

	return {@ x : x in partition | not IsEmpty(x) @};
end intrinsic;

intrinsic internal_Dis(M :: SeqEnum[SeqEnum[RngIntElt]]) -> GrpPerm
{ It should not be used by an external user : Finds the displacement group of the quandle represented by the integral quandle matrix M }
	
	S_X := Sym(#M);
	
	return sub< S_X | [ ((S_X ! x)) * ((S_X ! y)^-1): x,y in M ] >;
end intrinsic;

intrinsic internal_Dis_a(M :: SeqEnum[SeqEnum[RngIntElt]], alpha :: SetIndx[SetEnum[RngIntElt]]) -> GrpPerm
{ Finds the displacement group of the quandle represented by the integral quandle matrix M relative to congruence alpha represented by its induced partion of the underlying set of the quandle }

	error if not internal_hasCompatibilityProperty(M, alpha), "This equivalence relation does not have the compatibility property.";
	S_X := Sym(#M);

	Sym_elements := [ ];
	for block in alpha do
		generating_permutations := [ ((S_X ! M[x])) * ((S_X ! M[y])^-1): x,y in block];
		Sym_elements := Sym_elements cat generating_permutations;
	end for;

	return sub< S_X | Sym_elements >;
end intrinsic;

intrinsic internal_Kernel_a(Q :: SeqEnum[SeqEnum[RngIntElt]], alpha :: SetIndx[SetEnum[RngIntElt]]) -> SetEnum
{ It should not be used by an external user : Returns the kernel relative to the congruence alpha represented by its induced partion of the underlying set of the quandle represented by Q }
	
	dis := internal_Dis(Q);
	
	ker_set := {};

	for h in dis do
		admittable := true;
		for index_a := 1 to #Q do
			ha := index_a^h;
			ok_round := false;
			for block in alpha do
				if ha in block and index_a in block then 
					ok_round := true;
					break;
				end if;
			end for;
			admittable := admittable and ok_round;
		
			if not admittable then 
				break;
			end if;
		end for;

		if admittable then 
			Include(~ker_set, h);
		end if;
		
	end for;
	
	return ker_set;
	
end intrinsic;

intrinsic internal_hasCompatibilityProperty(Q :: SeqEnum[SeqEnum[RngIntElt]], alpha :: SetIndx[SetEnum[RngIntElt]]) -> BoolElt
{ It should not be used by an external user : Verifies whether the equivalence relation induced by alpha has the compatibility property as defined in A COURSE IN UNIVERSAL ALGEBRA by S. BURRIS and H. P. SANKAPPANAVAR }
	
	for block in alpha do
		results := { Q[x,y] : x, y in block };
		if results notin alpha then 
			return false;
		end if;
	end for;

	return true;
end intrinsic;

intrinsic internal_IsCongruence_semiregular(G :: GrpPerm, alpha :: SetIndx[SetEnum[RngIntElt]]) -> QuoQndl
{ It should not be used by an external user : Checks that for every g in G, if g(a) = a then g(b) = b for every b alpha a; alpha is the partition induced by a congruence relation }
	
	for g in G do
		for block in alpha do
			property_block := [ y^g eq y : y in block];
				
			if property_block ne [ property_block[1] : y in property_block] then 
				return false;
			end if;
		end for;
	end for;
	return true;
end intrinsic;

// The following function are a MAGMA translation of CREAM (possibly adapted to work specifically/only on Quandles) presented in 
// [CRP1] CREAM: A PACKAGE TO COMPUTE [AUTO, ENDO, ISO, MONO, EPI]-MORPHISMS, CONGRUENCES, DIVISORS AND MORE FORE ALGEBRA OF TYPE (2^n, 1^n)

intrinsic internal_UnarifyOperation(M :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SeqEnum[RngIntElt]]
{ Returns a sequence containing all the distinct unary operations on X induced by the binary operation of the quandle represented by M }

    UnaryOperations := [];
    for index_1 := 1 to #M do

        row := [];
        column := [];

        for index_2 := 1 to #M do
            resultrow := M[index_1, index_2];
            resultcolumn := M[index_2, index_1];
            Append(~row, resultrow);
            Append(~column, resultcolumn);
        end for;

        Include(~UnaryOperations, column);
        Include(~UnaryOperations, row);
        
    end for;
    
    return UnaryOperations;
end intrinsic;

intrinsic internal_ContainedPartition(partition1 :: SeqEnum[RngIntElt], partition2 :: SeqEnum[RngIntElt]) -> BoolElt
{ Returns True if partition1 is contained in partition2, False otherwise }
    for index_1 := 1 to #partition1 do
        if partition1[index_1] lt 0 then
            if partition2[index_1] lt 0 then 
                block2 := index_1;
            else
                block2 := partition2[index_1];
            end if;
            for index_2 := index_1+1 to #partition1 do
                if (partition1[index_2] eq index_1) and (block2 ne partition2[index_2]) then
                    return false;
                end if;
            end for;
        end if;
    end for;

    return true;

end intrinsic;

intrinsic internal_RootBlock(x :: RngIntElt, ~partition :: SeqEnum[RngIntElt], ~root :: RngIntElt) 
{ Sets root to the the root of the block containing element x }
    
    root := x;
    while partition[root] ge 0 do
        root := partition[root];
    end while;
    if x ne root then 
        partition[x] := root;
    end if;
end intrinsic;

intrinsic internal_JoinBlocks(x :: RngIntElt, y :: RngIntElt, ~partition :: SeqEnum[RngIntElt])
{ Joins the blocks containing x and y in partition }

    root1 := 0;
    internal_RootBlock(x, ~partition, ~root1);

    root2 := 0;
    internal_RootBlock(y, ~partition, ~root2);

    if root1 ne root2 then
        if partition[root1] lt partition[root2] then
            partition[root1] := partition[root1] + partition[root2];
            partition[root2] := root1;
        else
            partition[root2] := partition[root1] + partition[root2];
            partition[root1] := root2;
        end if;
    end if;
end intrinsic;

intrinsic internal_NumberOfBlocks(partition :: SeqEnum[RngIntElt]) -> RngIntElt
{ Returns the number of block in the encoded partition }
    return #([x : x in partition | x lt 0]);
end intrinsic;

intrinsic internal_NormalisePartition(~partition :: SeqEnum[RngIntElt])
{ Normalises partition }
    
    for index := 1 to #partition do
        root := 0;
        internal_RootBlock(index, ~partition, ~root);
        
        if root ge index then 
            partition[index] := -1;
            if root gt index then 
                partition[root] := index;
            end if;
        else
            partition[root] := partition[root] - 1;
        end if;
    end for;  
    
end intrinsic;

intrinsic internal_JoinPartitions(~partition1 :: SeqEnum[RngIntElt], ~partition2 :: SeqEnum[RngIntElt])
{ Turns partition2 into the smallest partition containing both partition1 and partition2 }
    
    for index := 1 to #partition1 do
        root := 0;
        internal_RootBlock(index, ~partition1, ~root);
        internal_JoinBlocks(index, root, ~partition2);
    end for;   
    
end intrinsic;

intrinsic internal_ComparePartitions(partition1 :: SeqEnum[RngIntElt], partition2 :: SeqEnum[RngIntElt]) -> RngIntElt
{ Compares partition1 and partition2 and returns: 0 if partition1 = partition2; 1 if partition1 < partition2; -1 if partition1 > partition2 }
    for index := 1 to (#partition1 - 1) do
        if partition1[index] lt partition2[index] then
            return 1;
        end if;
        if partition1[index] gt partition2[index] then
            return -1;
        end if;
    end for;  
    return 0;  
end intrinsic;

intrinsic internal_PrincipalCongruence(F :: SeqEnum[SeqEnum[RngIntElt]], GeneratingPair :: Tup) -> SeqEnum[RngIntElt]
{ It returns the principal congruence generated by a and b in the quandle represented by the integral quandle matrix F }
    Pairs := [ GeneratingPair ];
    congruence := [ -1 : x in F[1] ];
    internal_JoinBlocks(GeneratingPair[1], GeneratingPair[2], ~congruence); 
    
    while not IsEmpty(Pairs) do
        Pair := Pairs[1];
        Remove(~Pairs, 1);
        for f in F do
            root1 := 0;
            internal_RootBlock(f[Pair[1]], ~congruence, ~root1);

            root2 := 0;
            internal_RootBlock(f[Pair[2]], ~congruence, ~root2);

            if root1 ne root2 then 
                internal_JoinBlocks(root1, root2, ~congruence);
                Append(~Pairs, <root1, root2>);
            end if;

        end for;
    end while;
    internal_NormalisePartition(~congruence);
    return congruence;
end intrinsic;

intrinsic internal_AllPrincipalCongruences(F :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SeqEnum[SeqEnum[RngIntElt]]]
{ It returns all the principal congruences of the quandle represented by the integral quandle matrix F }
   congruences := [];


   for index_1 := 1 to ((#F[1]) - 1) do
        for index_2 := (index_1 + 1) to #F[1]  do
            congruence := internal_PrincipalCongruence(F, <index_1, index_2>);
            hash := Hash(congruence) mod 1000;
            hash := hash gt 0 select hash else 37;
            if IsDefined(congruences, hash) then 
                Include(~congruences[hash], congruence);
            else 
                congruences[hash] := [ congruence ];
            end if;
        end for;
    end for;
    return congruences;
end intrinsic;



intrinsic internal_CongruencesDisconnected(F :: SeqEnum[SeqEnum[RngIntElt]]) -> SetIndx[SeqEnum[RngIntElt]]
{ It returns all the congruences of A }

    PrincipalCongruences := internal_AllPrincipalCongruences(F);
    congruencesLookup := PrincipalCongruences;

    PrincipalCongruences := &cat [ PrincipalCongruences[x] : x in [1..#PrincipalCongruences] | IsDefined(PrincipalCongruences,x) ];
    congruences := PrincipalCongruences;
    
    index_1 := 1;
    while index_1 lt #congruences do
        for index_2 := 1 to #PrincipalCongruences do
            congruence := PrincipalCongruences[index_2];
            if not internal_ContainedPartition(congruence, congruences[index_1]) then 
                internal_JoinPartitions(~congruences[index_1], ~congruence);
                internal_NormalisePartition(~congruence);
                hash := Hash(congruence) mod 1000;
                hash := hash gt 0 select hash else 37;
                if IsDefined(congruencesLookup, hash) then 
                    if congruence notin congruencesLookup[hash] then 
                        Append(~congruencesLookup[hash], congruence);
                        Append(~congruences, congruence);
                    end if;
                else 
                    congruencesLookup[hash] := [ congruence ];
                    Append(~congruences, congruence);
                end if;
            end if; 
        end for;
        index_1 := index_1+1;
    end while;
    return congruences;
end intrinsic;



// invariants 2, 3, 4, 6, 11
intrinsic internal_Invariants(F :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SeqEnum[RngIntElt]]
{ It returns the vector of invariants of the quandle represented by F }
    QSet := [1..#F];


    Q_invariants := [];

    for p in QSet do
        invariants := [0, 0, 0, 0, 0];

        inv6 := {};


        for x in QSet do
            px := F[p][x];

            if px eq x then
                invariants[1] +:= 1;
            end if;

            xp := F[x][p];

			Include(~inv6,xp);
//             Include(~inv6,px);

            if xp eq x then
                invariants[2] +:= 1;
            end if;

            if F[px][p] eq p then
                invariants[3] +:= 1;
            end if;

            if xp eq px then
                invariants[5] +:= 1;
            end if;

        end for;

        invariants[4] := #inv6;

        Append(~Q_invariants,invariants);
    end for;

    QInvSet := SetToIndexedSet(Set(Q_invariants));

    partition := [ [ [], x ]: x in QInvSet ]; // Cannot use tuples because it causes problems with the universe when appending

    for index1 in QSet do
        for index2 := 1 to #partition do
            if Q_invariants[index1] eq QInvSet[index2] then
                Append(~partition[index2,1], index1);

                break;
            end if;
        end for;
    end for;

    return partition;
end intrinsic;


intrinsic internal_ElementInvariants(F :: SeqEnum[SeqEnum[RngIntElt]], p :: RngIntElt) -> SeqEnum[RngIntElt]
{ It returns the vector of invariants of the element p of F }
    QSet := [1..#F];


    invariants := [0, 0, 0, 0,  0];

    inv6 := {};


    for x in QSet do
        px := F[p][x];

        if px eq x then
            invariants[1] +:= 1;
        end if;

        xp := F[x][p];

		Include(~inv6,xp);
//         Include(~inv6,px);

        if xp eq x then
            invariants[2] +:= 1;
        end if;

        if F[px][p] eq p then
            invariants[3] +:= 1;
        end if;

        if xp eq px then
            invariants[5] +:= 1;
        end if;

    end for;

    invariants[4] := #inv6;

    return invariants;
end intrinsic;