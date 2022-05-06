// Definition of the type for Quotient Quandles
declare type QuoQndl: Qndl;

// Definition of extra attributes for Quandles arisen from another Quandle and a congruence 
declare attributes QuoQndl: Quandle, Congruence;


/*
 * Input: A square sequence of sequences M, representing a quandle.
 *
 * Output: The displacement group of the quandle represented by M
 */
intrinsic Dis(M :: SeqEnum[SeqEnum[RngIntElt]]) -> GrpPerm
{ Finds the displacement group of the quandle represented by M }
	
	
	// Creates the symmetric group for n = Number of rows of M, because it expects that the underlying set of the quandle Q represented by the integral quandle matrix M is {1, 2, ..., n}.
	S_X := Sym(#M);
	
	// Transforms each permutation(Lx^-1(X) and Ly(X)), where X is the underlying set of the quandle) into an element of the symmetric group, multiplies them and add the result Lx^-1Ly to the list
	Sym_elements := [ ((S_X ! x)) * ((S_X ! y)^-1): x,y in M ];
	
	// Generates the Permutation Group with the permutations found above as generators.
	return sub< S_X | Sym_elements >;
end intrinsic;


/*
 * Input: Let A = <X = {1, 2, ..., n}, F> be a binary algebra with a single operation, for some n in N. 
 * F : The binary operation of the algebra by a square sequence of sequences.
 * alpha : An equivalence alpha represented by an indexed set of indexed sets. 
 * 
 *
 * Output: 
 * True if alpha has the compatibility property, False otherwise.
 */
intrinsic hasCompatibilityProperty(F :: SeqEnum[SeqEnum[RngIntElt]], alpha :: SetIndx[SetIndx[RngIntElt]]) -> BoolElt
{ Verifies whether the equivalence relation induced by alpha has the compatibility property as defined in A COURSE IN UNIVERSAL ALGEBRA by S. BURRIS and H. P. SANKAPPANAVAR }
	
	error if #alpha gt #F, "This is not a partition of X.";
	
	for block in alpha do
		results := { F[x,y] : x, y in block };
		if results notin alpha then 
			return false;
		end if;
	end for;

	return true;
end intrinsic;


/*
 * N. Carrivale
 * Input:  
 * A partition pi of X = {1,2 ... n} encoded as explained in either CRP1 or HUTCHINSON.
 * kind : a flag with value in {true, false}; true for CRP1, false for HUTCHINSON.
 *
 * Output: pi decoded.
 */
intrinsic DecodePartition(pi :: SeqEnum[RngIntElt], kind :: BoolElt) -> SetIndx[SetIndx[RngIntElt]]
{ It decodes a partition of some set X encoded as explained in CRP1 or in HUTCHINSON }

    partition := [ ];

    if kind then 
		
		for index := 1 to #pi do
			block := pi[index];

			try 
				if  partition[block] ne {@ @} then 
					Include(~partition[block], index);
				end if;
			catch noBlockError 
				partition[block] := {@ index @};
			end try;

		end for;

		
	else 
		// Loops over the "encoded" elements
		for index := 1 to #pi do
			// A values being less than 0 indicates a root
			if pi[index] lt 0 then
				// Creates a block with the root as first element
				Append(~partition, {@ index @});
				/*
				* Loops over the remaining elements of the encoded partition.
				* This is possible because for any encoded block, the root is always the first element to appear in the encoding
				* hence other elements of the block will only appear after the root
				*/
				for element_index := index+1 to #pi do
					if pi[element_index] eq index then
						Include(~partition[#partition], element_index);
					end if;
				end for;
			end if;
		end for;
	end if;

	return {@ block : block in partition | block ne {@ @} @};

end intrinsic;


/*
 * Input: 
 * A square sequence of sequences M, representing a quandle.
 * alpha: A congruence alpha encoded as explained in either CRP1 or HUTCHINSON.
 * kind : a flag with value in {true, false}; true for CRP1, false for HUTCHINSON.
 *
 *
 * Output: The displacement group of A relative to congruence alpha
 */
intrinsic Dis_a(M :: SeqEnum[SeqEnum[RngIntElt]], alpha :: SeqEnum[RngIntElt], kind :: BoolElt) -> GrpPerm
{ Finds the displacement group of A relative to congruence alpha }

	return Dis_a(M, DecodePartition(alpha,kind));
end intrinsic;

/*
 * Input: 
 * A square sequence of sequences M, representing a quandle.
 * alpha: A congruence alpha.
 *
 *
 * Output: The displacement group of A relative to congruence alpha
 */
intrinsic Dis_a(M :: SeqEnum[SeqEnum[RngIntElt]], alpha :: SetIndx[SetIndx[RngIntElt]]) -> GrpPerm
{ Finds the displacement group of A relative to congruence alpha }

	error if not hasCompatibilityProperty(M, alpha), "This equivalence relation does not have the compatibility property.";

	// Creates the symmetric group for n = Number of rows of M, because it expects that the underlying set of the quandle Q represented by the integral quandle matrix M is {1, 2, ..., n}.
	S_X := Sym(#M);


	Sym_elements := [ ];

	for block in alpha do
		generating_permutations := [ ((S_X ! M[x])) * ((S_X ! M[y])^-1): x,y in block];
		Sym_elements := Sym_elements cat generating_permutations;
	end for;

	
	// Generates the Permutation Group with the permutations found above as generators.
	return sub< S_X | Sym_elements >;
end intrinsic;

/*
 * Input: 
 * A Quandle Q,
 * alpha: A congruence alpha encoded as explained in either CRP1 or HUTCHINSON.
 * kind : a flag with value in {true, false}; true for CRP1, false for HUTCHINSON.
 *
 *
 *
 * Output: The Quotient Quandle Q/alpha.
 */
intrinsic QuotientQuandle(Q :: Qndl, alpha :: SeqEnum[RngIntElt], kind :: BoolElt) -> QuoQndl
{ It generates the quotient quandle Q/alpha }
	return QuotientQuandle(Q, DecodePartition(alpha, kind));
end intrinsic;

/*
 * Input: 
 * A Quandle Q,
 * A congruence alpha represented by an encoded normalised partition.
 *
 *
 * Output: The Quotient Quandle Q/alpha.
 */
intrinsic QuotientQuandle(Q :: Qndl, alpha :: SetIndx[SetIndx[RngIntElt]]) -> QuoQndl
{ It generates the quotient quandle Q/alpha }

	error if not hasCompatibilityProperty(QuandleMatrix(Q), alpha), "This equivalence relation does not have the compatibility property.";

	// Creates the Quandle
    T := New(QuoQndl);

	T`Quandle := Q;
	T`Congruence := alpha;

	element_partition := [];
    for index in [1 .. # alpha] do
		element_partition[index] := [];
		for element in alpha[index] do
			Append(~element_partition[index], Q`Set[element]);
		end for;
	end for;

	find_block := function(partition, element)
					for index in [1 .. # alpha] do
						for element_in in alpha[index] do
							if element_in eq element then
								return index;
							end if;
						end for;
					end for;
					return 0;
				   end function;

	T`Set := [ block[1] : block in element_partition ];

	index_for_element := function(sequence, element)
                            for index in [1 .. # sequence] do
                                if (sequence[index] eq element) then
                                    return index;
                                end if;
                            end for;
                            return 0;
                         end function;


	graph := [ <<x, y>, index_for_element(T`Set, element_partition[find_block(element_partition, Q`Operation(<x, y>))][1])> : x,y in T`Set ];
	
	
	T`Operation := map< car<T`Set,T`Set> -> [1 .. # T`Set ] | graph >;


	// If, for any reason, the provided set and this operation do not form a quandle, the function will not return anything.
	require isQuandle(QuandleMatrix(T)): "The provided set does not generate a quandle with this associated operation.";
        
    return T;
end intrinsic;


/*
 * This is a modern implementation of the first algorithm in PARTITIONING ALGORITHMS FOR FINITE SETS by GEORGE HUTCHINSON
 * Input: Let X = {1 .. n}, for n in N.
 * n.
 *
 * Output: A list of all the partitions of X in lexicographic order.
 */
intrinsic PartitionSet(n :: RngIntElt) -> SeqEnum[RngIntElt]
{ Returns a list of all the partitions of X in lexicographic order }
	
	current := [];
	support := [];

	for index := 1 to n do
		current[index] := 1;
		support[index] := 1;
	end for;
	
	partitions := [current];
	
	
	done := Bell(n);

	for index := 2 to done do
		increasable := n;

		while current[increasable] gt support[increasable] do
			increasable := increasable-1;
		end while;

		if increasable ne 1 then 
			current[increasable] := current[increasable] + 1;

			m := Max(current[increasable], support[increasable]);

			for replace_index := increasable+1 to n do
				current[replace_index] := 1;
				support[replace_index] := m;
			end for;
		end if;

		
		partitions[index] := current;

	end for;

	return partitions;
	
end intrinsic;


/*
 * Input: 
 * A quandle Q
 * A congruence alpha represented by a partition, encoded according to PARTITIONING ALGORITHMS FOR FINITE SETS by GEORGE HUTCHINSON,
 * or as a set of sets.
 * kind : a flag with value in {true, false}; true for CRP1, false for HUTCHINSON - relevant only when the ExtendedType of alpha is SeqEnum[RngIntElt].
 *
 *
 * Output: The kernel relative to the congruence 'alpha', Dis^a.
 */
intrinsic Kernel_a(Q :: SeqEnum[SeqEnum[RngIntElt]], alpha :: . , kind :: BoolElt) -> SetEnum
{ Returns the kernel relative to the congruence 'alpha' }
	
	error if ExtendedType(alpha) notin [SeqEnum[RngIntElt], SetIndx[SetIndx[RngIntElt]]], "This partition is not of the right type";

	sets := ExtendedType(alpha) eq SetIndx[SetIndx[RngIntElt]];

	dis := Dis(Q);

	ker_set := {};
	
	uSet := [1 .. #Q];
	
	for h in dis do
		admittable := true;
		for index_a := 1 to #Q do
			ha := Eltseq(h)[index_a];
			
			if sets then 
				ok_round := false;
				for block in alpha do
					if ha in block and index_a in block then 
						ok_round := true;
						break;
					end if;
				end for;
				admittable := admittable and ok_round;
			else
				if kind then 
					root1, _ := RootBlock(ha, alpha);
					root2, _ := RootBlock(index_a, alpha);
					admittable := admittable and (root1 eq root2);
				else 
					admittable := admittable and (alpha[ha] eq alpha[index_a]);
				end if;

			end if;

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



/* TO BE VERIFIED: alpha^InnQ
 * Input: 
 * A quandle Q, represented a sequence of sequences
 * A congruence alpha represented by a partition.
 *
 * Output: True, if alpha represents a congruence of Q; False, otherwise. 
 */
intrinsic isCongruenceLemma1_5(Q :: SeqEnum[SeqEnum[RngIntElt]], alpha :: SetIndx[SetIndx[RngIntElt]]) -> BoolElt
{ Returns the equivalence relation 'alpha' is a congruence }

	
	InnQ := Inn(Q);
	
	result := (alpha^InnQ) ;

	if #result ne 1 then 
		return false;
	else 
		if alpha ne result[1] then 
			return false;
		end if;
	end if;

	
	Dis_ua := Kernel_a(Q, alpha, true);

	// Creates the symmetric group for n = Number of rows of M, because it expects that the underlying set of the quandle Q represented by the integral quandle matrix M is {1, 2, ..., n}.
	S_X := Sym(#Q);


	Sym_elements := [ ];

	for block in alpha do
		for x,y in block do
			permutation := ((S_X ! Q[x])) * ((S_X ! Q[y])^-1);
			if permutation notin Dis_ua then 
				return false;
			end if;
		end for;
	end for;
	

	
	

	
	return true;
end intrinsic;

/* TO BE VERIFIED
 * Input: 
 * A square sequence of sequences M, representing a quandle.
 * alpha: A congruence alpha encoded as explained in either CRP1 or HUTCHINSON.
 * kind : a flag with value in {true, false}; true for CRP1, false for HUTCHINSON.
 *
 * Output: True, if alpha represents a congruence of Q; False, otherwise. 
 */
intrinsic isCongruenceLemma1_5(Q :: SeqEnum[SeqEnum[RngIntElt]], alpha :: SeqEnum[RngIntElt], kind :: BoolElt) -> BoolElt
{ Returns the equivalence relation 'alpha' is a congruence }

return isCongruenceLemma1_5(Q, DecodePartition(alpha, kind));
	
end intrinsic;

/*
 * Input: 
 * A quandle Q
 *
 * Output: All the congruences of Q.
 */
intrinsic AllCongruencesLemma1_5(Q :: Qndl) -> SetEnum
{ Returns all the congruences of Q }
	return AllCongruencesLemma1_5(QuandleMatrix(Q));
	
end intrinsic;


/*
 * Input: 
 * A quandle Q
 *
 * Output: All the congruences of Q.
 */
intrinsic AllCongruencesLemma1_5(Q :: SeqEnum[SeqEnum[RngIntElt]]) -> SetIndx[SeqEnum[RngIntElt]]
{ Returns all the congruences of Q }
	Partitions := PartitionSet(#Q);

	congruences := {@ @};
	for partition in Partitions do
		if isCongruenceLemma1_5(Q, partition, true) then 
			Include(~congruences, partition);
		end if;
	end for;

	return congruences; 
	
end intrinsic;