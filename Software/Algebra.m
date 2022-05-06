// This is mostly a MAGMA translation of CREAM (possibly adapted to work specifically/only on Quandles) presented in 
// [CRP1] CREAM: A PACKAGE TO COMPUTE [AUTO, ENDO, ISO, MONO, EPI]-MORPHISMS, CONGRUENCES, DIVISORS AND MORE FORE ALGEBRA OF TYPE (2^n, 1^n)

// I added some extra functions to make life easier.

// Contrary to COMPUTING CONGRUENCES EFFICIENTLY by RALPH FREESE, the root of a tree(block of a partition) here is the minimum element.


/* 
 * N. Carrivale
 * Input: 
 * A partition pi of X = {1,2 ... n}, for n in N - as a sequence of sequences.
 * sort : a flag to indicate whether the block must be sorted or not.
 * 
 * Output: pi encoded as explained in CRP1. 
 */
intrinsic EncodePartition(pi :: SeqEnum[SeqEnum[RngIntElt]], sort :: BoolElt) -> SeqEnum[RngIntElt]
{ It encodes a partition of some set X as explained in CRP1 }

    // Creates the sequence that will hold the encoded partition
    encoding := [];
    
    // Loops over all the blocks of the partition
    for index_1 := 1 to #pi do

        block := pi[index_1];


        // Sorts the block if necessary - the minimum element must be the first element of a block
        block := sort select Sort(block) else block;
        
        /*
         * Loops over all the blocks after the current block;
         * This is enough because we know that "disjoint-ness" with precedent blocks has already been verified.
         */
        for index_2 := index_1+1 to #pi  do
            block2 := pi[index_2];
            for element in block2 do
                error if element in block, "The elements of this sequence are not pairwise disjoint.";
            end for;
        end for;
        
        // In the unlikely event that a partition contains an empty block, this makes the computation continue elegantly
        try
            encoding[block[1]] := - (#block);
        catch empty
            continue;
        end try;

        for index_2 := 2 to #block do
            encoding[block[index_2]] := block[1];
        end for;

    end for;

    

    return encoding;

end intrinsic;

/*
 * N. Carrivale
 * Input:  A partition pi of X = {1,2 ... n}, for n in N - as a set of sets.
 *
 *
 * Output: pi encoded as explained in CRP1.
 */
intrinsic EncodePartition(pi :: SetEnum[SetEnum[RngIntElt]]) -> SeqEnum[RngIntElt]
{ It encodes a partition of some set X as explained in CRP1 }


    // Turns a set of sets into a set of sequences
    seqseqs := [];
    for element in pi do
        Append(~seqseqs, Sort(Setseq(element)));
    end for;

    return EncodePartition(seqseqs, false);
    
end intrinsic;

/* 
 * N. Carrivale
 * Input: M, A binary operation on X = {1,2 ... n}, represented by a sequence of sequences, for n in N.
 * 
 *
 * Output: It returns a sequence containing all the distinct unary operations on X induced by the (possibly) binary operations on X in F.
 */
intrinsic UnarifyOperation(M :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SeqEnum[RngIntElt]]
{ Returns a sequence containing all the distinct unary operations on X induced by the binary operation. }

    /*
     * The algorithm described by Ralph Freese in COMPUTING CONGRUENCES EFFICIENTLY
     * only works with unary algebras, that is, algebras with only unary operations.
     *
     * Hence we need to convert binary operatio to 2n unary operations where n is the cardinality of X.
     */

    /* 
     * Let M =
     * 
     *   _              _
     *  | a11 a12 .. a1n |
     *  | a21 a22 .. a2n |
     *  |  .   .  ..  .  |
     *  | an1 an2 .. ann |
     *   -              -
     */
    
   
    X := [1 .. #M];

   
    UnaryOperations := [];
    for index_1 := 1 to #M do

        row := [];
        column := [];

        for index_2 := 1 to #M do
            

            try 
                resultrow := M[index_1, index_2];
                resultcolumn := M[index_2, index_1];
            catch IndexError
                error "This operation is not defined properly";
            end try;

            

            

            /* 
             * Let index_1 be i and index_2 be j.
             * row := [ ai1 ai2 .. ain ]
             * column := [ aj1 aj2 .. ajn ]
             */
            Append(~row, resultrow);
            Append(~column, resultcolumn);
        end for;

        // Checks whether the two unary operations are the same
        same := row eq column;

        // If this operation has not already been seen, it is added to the list
        if row notin UnaryOperations then 
            Append(~UnaryOperations, row);
        end if;
        

        // If this operation has not already been seen, it is added to the list
        if (not same) and (column notin UnaryOperations) then 
            Append(~UnaryOperations, column);
        end if;
        
    end for;
    
    

    
    return UnaryOperations;
end intrinsic;


/* 
 * N. Carrivale
 * Input: Let A = <X = {1, 2, ..., n}, F> be an algebra, for some n in N. 
 * F : A sequence of operations on X represented by sequences of sequences.
 * 
 * Output: It returns a sequence containing all the distinct unary operations on X induced by the binary operations on X in F.
 * Note: Since the goal of this project is to work with quandles we only need to handle one binary operation but 
 * the translation of CREAM into MAGMA might be useful to us or other people so I am trying to keep things as general as possible
 * where doing it is easy enough. 
 */
intrinsic UnarifyAlgebra(F :: SeqEnum[SeqEnum[SeqEnum[RngIntElt]]]) -> SeqEnum[SeqEnum[RngIntElt]]
{ Returns a sequence containing all the distinct unary operations on X induced by the binary operations on X in F. }

    
    
    // Creates the list where the unary operations will be stored
    unarifiedOperations := [];

    last := #F[1];

    for f in F do
        // Checks that the cardinality of the sets on which the function are supposed to operate is always the same
      
        error if #f ne last, "The sequence contains functions with different domains. ";
        

        

        unarifiedOperation := UnarifyOperation(f);

        // After the binary operation has been unarified, it verifies that the induced unary operations have not already been seen.
        unarifiedOperations := IsSubsequence(unarifiedOperation, unarifiedOperations: Kind := "Setwise") select unarifiedOperations else (unarifiedOperation cat unarifiedOperations);
    end for;

    return unarifiedOperations;
end intrinsic;



/*
 * CREAM
 * Input: 
 * An encoded normalised partition partition1(sub-partition).
 * An encoded normalised partition partition2(super-partition).
 *
 * Output:  True if partition1 is contained in partition2, False otherwise.
 */
intrinsic ContainedPartition(partition1 :: SeqEnum[RngIntElt], partition2 :: SeqEnum[RngIntElt]) -> BoolElt
{ Returns True if partition1 is contained in partition2, False otherwise. }
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

/*
 * CREAM
 * Input: Let X = {1, 2, ..., n}, for some n in N.
 * Element x in X.
 * A partition 'partition' of X, pi(X).
 *
 *
 * Output: returns the root node of the block containing node x and a possibly more shallow partition.
 * Note: Reference parameters are only allowed in procedures.
 */
intrinsic RootBlock(x :: RngIntElt, partition :: SeqEnum[RngIntElt]) -> RngIntElt, SeqEnum[RngIntElt]
{ Returns the root node of the block containing node x }
    require x gt 0: "i must be greater than 0.";
    require partition ne []: "This partition is empty.";

    index := x;
    while partition[index] ge 0 do
        index := partition[index];
    end while;
    if x ne index then 
        partition[x] := index;
    end if;
    return index, partition;

end intrinsic;

/*
 * CREAM
 * Input: Let X = {1, 2, ..., n}, for some n in N.
 * Element x of X.
 * Element y of X.
 * A partition 'partition' of X.
 *
 *
 * Output: Returns a partition where the blocks containing x and y have been joined. 
 */
intrinsic JoinBlocks(x :: RngIntElt, y :: RngIntElt, partition :: SeqEnum[RngIntElt]) -> SeqEnum[RngIntElt]
{ Returns a partition where the blocks containing x and y have been joined }
    
    require x le #partition : "x is not in X.";
    require y le #partition : "y is not in X.";

    root1, partition := RootBlock(x, partition);

    root2, partition := RootBlock(y, partition);
    

    if root1 ne root2 then
        if partition[root1] lt partition[root2] then
            partition[root1] := partition[root1] + partition[root2];
            partition[root2] := root1;
        else
            partition[root2] := partition[root1] + partition[root2];
            partition[root1] := root2;
        end if;
    end if;
    return partition;
end intrinsic;


/*
 * CREAM
 * Input: A partition 'partition' of X = {1, 2, ..., n}, for some n in N.
 *
 *
 * Output: Returns the number of blocks in 'partition'. 
 */
intrinsic NumberOfBlocks(partition :: SeqEnum[RngIntElt]) -> RngIntElt
{ Returns the number of block in the encoded partition }
    return #([x : x in partition | x lt 0]);
end intrinsic;

/*
 * CREAM
 * Input: A partition 'partition' of of X = {1, 2, ..., n}, for some n in N.
 *
 *
 * Output: Returns a partition(disjoint forest) where each block(tree) has its minimum element as root 
 * and each non-root node is directly conncted its root; such a partition is a normalised partition.
 */
intrinsic NormalisePartition(partition :: SeqEnum[RngIntElt]) -> SeqEnum[RngIntElt]
{ Returns the normalised version of 'partition' }
    
    for index := 1 to #partition do
        root, partition := RootBlock(index, partition);
        
        if root ge index then 
            partition[index] := -1;
            if root gt index then 
                partition[root] := index;
            end if;
        else
            partition[root] := partition[root] - 1;
        end if;
    end for;  
    return partition;  
end intrinsic;

/*
 * CREAM
 * Input: 
 * A partition 'partition1' of X = {1, 2, ..., n}, for some n in N.
 * A partition 'partition2' of Y = {1, 2, ..., h}, for some h in N.
 *
 * Output: Returns the smallest partition containing both partition1 and partition2.
 */
intrinsic JoinPartitions(partition1 :: SeqEnum[RngIntElt], partition2 :: SeqEnum[RngIntElt]) -> SeqEnum[RngIntElt]
{ Returns the smallest partition containing both partition1 and partition2. }
    
    for index := 1 to #partition1 do
        root, partition1 := RootBlock(index, partition1);
        partition2 := JoinBlocks(index, root, partition2);
    end for;   
    return NormalisePartition(partition2);
end intrinsic;


/*
 * CREAM
 * Input: 
 * A normalised partition 'partition1' of X = {1, 2, ..., n}, for some n in N.
 * A normalised partition 'partition2' of Y = {1, 2, ..., h}, for some h in N.
 *
 * Output: 
 *  0 if partition1 = partition2
 *  1 if partition1 < partition2
 * -1 if partition1 > partition2
 */
intrinsic ComparePartitions(partition1 :: SeqEnum[RngIntElt], partition2 :: SeqEnum[RngIntElt]) -> RngIntElt
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

/*
 * CREAM & COMPUTING CONGRUENCES EFFICIENTLY by R. Freese
 * Input: Let A = <X = {1, 2, ..., n}, F> be a unary or "unarified" algebra, for some n in N.
 * F : A sequence of operations on X represented by sequences of sequences.
 * A pair <a, b> with a, b in X.
 *
 *
 * Output: The principal congruence generated by a and b in A.
 */
intrinsic PrincipalCongruence(F :: SeqEnum[SeqEnum[RngIntElt]], GeneratingPair :: Tup) -> SeqEnum[RngIntElt]
{ It returns the principal congruence generated by a and b in A }
    Pairs := [ GeneratingPair ];

    congruence := EncodePartition(Partition([1 .. #F[1]],1), false);
    congruence := JoinBlocks(GeneratingPair[1], GeneratingPair[2], congruence); 
    
    while not IsEmpty(Pairs) do
        Pair := Pairs[1];
        Remove(~Pairs, 1);
        for f in F do
            root1, congruence := RootBlock(f[Pair[1]], congruence);
            
            root2, congruence := RootBlock(f[Pair[2]], congruence);
            
            if root1 ne root2 then 
                congruence := JoinBlocks(root1, root2, congruence);
                Append(~Pairs, <root1, root2>);
            end if;

        end for;
    end while;
    return NormalisePartition(congruence);
end intrinsic;




/*
 * CREAM
 * Input: Let A = <X = {1, 2, ..., n}, F> be a unary or "unarified" algebra, for some n in N.
 *  F : A sequence of operations on X represented by sequences of sequences.
 *
 *
 * Output: All the principal congruences of A.
 */
intrinsic AllPrincipalCongruences(F :: SeqEnum[SeqEnum[RngIntElt]]) -> SetIndx[SeqEnum[RngIntElt]]
{ It returns all the principal congruences in A }
   congruences := {@ @};
   for index_1 := 1 to ((#F[1]) - 1) do
        for index_2 := (index_1 + 1) to #F[1]  do
            congruence := PrincipalCongruence(F, <index_1, index_2>);

            Include(~congruences, congruence);
            
        end for;
    end for;
    return congruences;
end intrinsic;


/*
 * CREAM
 * Input: Let A = <X = {1, 2, ..., n}, F> be a unary or "unarified" algebra, for some n in N.
 *  F : A sequence of operations on X represented by sequences of sequences.
 *
 *
 * Output: All the congruences of A.
 */
intrinsic AllCongruences(F :: SeqEnum[SeqEnum[RngIntElt]]) -> SetIndx[SeqEnum[RngIntElt]]
{ It returns all the congruences of A }

   PrincipalCongruences := AllPrincipalCongruences(F);

   congruences := PrincipalCongruences;

   index_1 := 1;
   while index_1 lt # congruences do
        for index_2 := 1 to # PrincipalCongruences do
            if not ContainedPartition(PrincipalCongruences[index_2], congruences[index_1]) then 
                congruence := JoinPartitions(PrincipalCongruences[index_2], congruences[index_1]);
                Include(~congruences, congruence);
            end if; 
        end for;
        index_1 := index_1+1;
    end while;
    return congruences;
end intrinsic;

/*
 * CREAM
 * Input: A quandle, F.
 *
 *
 * Output: All the congruences of F.
 */
intrinsic AllCongruences(F :: Qndl) -> SetIndx[SeqEnum[RngIntElt]]
{ It returns all the congruences of F }

   return AllCongruences(UnarifyOperation(QuandleMatrix(F)));
end intrinsic;

/*
 * CREAM
 * Input: A quandle, F.
 *
 *
 * Output: A generating set for F.
 */
intrinsic EfficientGeneratingSet(F :: Qndl) -> SetEnum[RngIntElt]
{ It returns a generating set for F. }

    RSQM := QuandleMatrix(F);
    candidates := InvariantPartition(RSQM, InvariantMap(RSQM));

        
    return EfficientGeneratingSet(RSQM, candidates);
   
end intrinsic;




/*
 * CREAM
 * Input: Let A = <X = {1, 2, ..., n}, F> be binary algebra with a single operation.
 *  F : The binary operation on X represented by sequences of sequences.
 *  candidates: a partition of X.
 *
 *
 * Output: A generating set for A
 */
intrinsic EfficientGeneratingSet(F :: SeqEnum[SeqEnum[RngIntElt]], candidates :: SeqEnum[SeqEnum[RngIntElt]]) -> SetIndx[RngIntElt]
{ It returns a generating set for A }

    submagma := {};
    generator := {@ @};
    

        
    while #submagma ne #F do
        most := <0,0,{}>;
        for index_block := 1 to #candidates do
            for index_element := 1 to #candidates[index_block] do
                generated := generatedSet(generator join {@ candidates[index_block][index_element] @}, {@ @}, F);
                if #generated gt #most[3] then 
                     most := <index_block,index_element,generated>;
                end if;
            end for;
        end for;
        Include(~generator, candidates[most[1]][most[2]]);
        submagma := most[3];
        try 
            Remove(~candidates[most[1]],most[2]);
        catch error_index
            continue;
        end try;
    end while;

    return generator;
   
end intrinsic;


/*
 * CREAM + Niccolò Carrivale - Specific for quandles
 * Input: Let A = <X = {1, 2, ..., n}, F> be binary algebra with a single operation.
 *  F : The binary operation on X represented by sequences of sequences.
 *
 *
 * Output: A sequence S with n elements S[i] = [a, b, c, d, e] where 
 * a is the value of invariant 2 for the i-th element, 
 * b is the value of invariant 3 for the i-th element, 
 * c is the value of invariant 6 for the i-th element, and 
 * d is the value of invariant 11 for the i-th element.
 * e is the value of invariant 17 for the i-th element.
 */
intrinsic InvariantMap(F :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SeqEnum[RngIntElt]]
{ Returns the sequence containing the values of invariants 2, 3, 6, 11 and 17 in CR1 for each element of X }

    invariant_vector := [ ];
    partition_ := [];
    uSet := {};
    for index_1 := 1 to #F do
        
        invariant_2 := 0;
        invariant_3 := 0;
        invariant_6 := [];
        invariant_11 := 0;
        uSet := uSet meet { index_1 };
        for index_2 := 1 to #F do

            if F[index_1,index_2] eq index_2 then 
                invariant_2 := invariant_2 + 1;
            end if;

            if F[index_2,index_1] eq index_2 then 
                invariant_3 := invariant_3 + 1;
            end if;

            if F[index_1,index_2] eq F[index_2,index_1] then 
                invariant_11 := invariant_11 + 1;
            end if;

            if F[index_1,index_2] notin invariant_6 then 
                Append(~invariant_6, F[index_1, index_2]);
            end if;

        end for;

        invariant_vector[index_1] := [ invariant_2, invariant_3, #invariant_6, invariant_11 ];

    end for;

    subs := Subsets(uSet, 2);

    for index_1 := 1 to #F do

        invariant_17 := [];

        for t in subs do
            t_seq := [ x : x in t];

            a := F[t_seq[1]][t_seq[2]];
            b := F[t_seq[2]][t_seq[1]];
            if a eq index_1 and b notin invariant_17 then 
                Append(~invariant_17, b);
            end if;

            if b eq index_1 and a notin invariant_17 then 
                Append(~invariant_17, a);
            end if;

        end for;
        Append(~invariant_vector[index_1], #invariant_17);
    end for;
   
    return invariant_vector;
end intrinsic;

/*
 * CREAM + Niccolò Carrivale - Specific for quandles
 * Input: Let A = <X = {1, 2, ..., n}, F> be binary algebra with a single operation.
 *  F : The binary operation on X represented by sequences of sequences.
 *  Invariants : A sequence [x1, x2, ..., xn] inducing an equivalence relation.
 *
 * Output: The set X partitioned according to the equivalence relation induced by the sequence 'Invariants',
 * with blocks sorted by ascending block size.
 */
intrinsic InvariantPartition(F:: SeqEnum[SeqEnum[RngIntElt]], Invariants :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SeqEnum[RngIntElt]]
{ The set X partitioned according to the equivalence relation induced by the sequence 'Invariants' }
    
    
    seen := [];

    partition := [];

    for index := 1 to #Invariants do
        invariant := Invariants[index];
        in_seen := invariant in seen;
        if not in_seen then 
            Append(~seen,invariant);
            partition[#seen] := [ index ];
        else 
            block := Index(seen, invariant);
            Append(~partition[block], index);
        end if;
    end for;

    return partition;
end intrinsic;

/*
 * CREAM + Niccolò Carrivale 
 * Input: 
 *  A potential subquandle of M of cardinality n, F, 
 *  A quandle, M.
 *
 *
 * Output: 
 * [], if there is no monomorphism from F to M.
 * [ f(a_1), f(a_2), ..., f(a_n)] where a_i in F, for 1 <= i <= n.
 */
intrinsic Monomorphism(F :: Qndl, M :: Qndl) -> SeqEnum[RngIntElt]
{ Returns, if it exists, a monomorfism from F to M }

    return Monomorphism(QuandleMatrix(F), QuandleMatrix(M));
    
end intrinsic;


/*
 * CREAM + Niccolò Carrivale 
 * Input: Let A = <X = {1, 2, ..., n}, F> be a binary algebra with a single operation, for some n in N.
 * Let B = <Y = {1, 2, ..., m}, M> be a binary algebra with a single operation, for some m in N.
 * Let n <= m.
 *
 *  F : The binary operation on X represented by sequences of sequences.
 *  M : The binary operation on Y represented by sequences of sequences.
 *
 * Output: 
 * [], if there is no monomorphism from F to M.
 * [ f(a_1), f(a_2), ..., f(a_n)] where a_i in F, for 1 <= i <= n.
 */
intrinsic Monomorphism(F :: SeqEnum[SeqEnum[RngIntElt]], M :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[RngIntElt]
{ Returns, if it exists, a monomorfism from A to B }
    FInvMap := InvariantMap(F);
    MInvMap := InvariantMap(M);

    // Very small set - often no more than 3 elements 
    FGenSet := Setseq(EfficientGeneratingSet(F, InvariantPartition(F, FInvMap)));

    if #F gt #M then 
        return [];
    end if;
    
    mapsTo := [ [] : x in FGenSet  ];

    for index_M := 1 to #M do
        for index_mapsTo := 1 to #FGenSet do
            
            if FInvMap[FGenSet[index_mapsTo]] le MInvMap[index_M] then
                Append(~mapsTo[index_mapsTo],index_M);
            end if;

        end for;
    end for;

    for images in mapsTo do
        if IsEmpty(images) then 
            return [];
        end if;
    end for;


    monomorphism := ExtendMonomorphism(F, M, FGenSet, mapsTo, [ 0 : index in F ]);

    return monomorphism;
    
end intrinsic;




/*
 * CREAM + Niccolò Carrivale - This is a recursive function
 * Input: Let A = <X = {1, 2, ..., n}, F> be a binary algebra with a single operation, for some n in N.
 * Let B = <Y = {1, 2, ..., m}, M> be a binary algebra with a single operation, for some m in N.
 * Let n <= m.
 *
 *  F : The binary operation on X represented by sequences of sequences.
 *  M : The binary operation on Y represented by sequences of sequences.
 *  FGenSet : A generating set for A.
 *  Images : A sequence holding the possible images for the elements of FGenSet.
 *  morphism : A sequence that hold the current status of the morphism under construction such that morphism[i] indicates the image of i under the morphism. 
 *              f[i] = 0 indicates that an image has not yet been defined. 
 *
 * Output: 
 */
intrinsic ExtendMonomorphism(F :: SeqEnum[SeqEnum[RngIntElt]], M :: SeqEnum[SeqEnum[RngIntElt]], FGenSet :: SeqEnum[RngIntElt], Images :: SeqEnum[SeqEnum[RngIntElt]], morphism :: SeqEnum[RngIntElt] ) -> SeqEnum[RngIntElt]
{ TODO }
    
    
    
    if IsEmpty(FGenSet) then 
        OldElements := {};
        NewElements := { y : y in [1 .. #F] | morphism[y] ne 0 };

        
        while not IsEmpty(NewElements) do
           
            Products := [];
            for oldElement in OldElements do
                for newElement in NewElements do
                    Append(~Products, <oldElement, newElement>);
                    Append(~Products, <newElement, oldElement>);
                end for;
            end for;

            for newElementA in NewElements do
                for newElementB in NewElements do
                    Append(~Products, <newElementA, newElementB>);
                end for;
            end for;

            Results := {};

            for product in Products do
                a := product[1];
                b := product[2];
                result_in_A := F[a][b];
                result_in_B := M[morphism[a]][morphism[b]];
                    // Preserves injectivity
                if (morphism[result_in_A] eq 0) and (result_in_B notin morphism) then 
                    morphism[result_in_A] := result_in_B;
                    Results := Results join { result_in_A };
                else 
                    // verifies Def2.1* Universal Algebra - Morphism
                    if morphism[result_in_A] ne result_in_B then 
                        return [];
                    end if;
                end if;
            end for;

            OldElements := OldElements join NewElements;
            NewElements := Results diff OldElements;
            
        end while;
        return morphism;
    end if;

    preImage := FGenSet[ 1 ];
    Remove(~FGenSet, 1);
    Remove(~Images, 1);

    // Preserves injectivity
    availableImages := [ y : y in M[1] | y notin morphism ];
    

    for availableImage in availableImages do

        updatedMorphism := morphism;
        updatedMorphism[preImage] := availableImage;

        updatedMorphism := ExtendMonomorphism(F, M, FGenSet, Images, updatedMorphism);
        
        if updatedMorphism ne [] then 
            return updatedMorphism;
        end if;

    end for;

    return [];
end intrinsic;


/*
 * NOTE THE NAME OF THIS FUNCTION MIGHT *NOT* BE APPROPRIATE. CONSIDER IT A PLACEHOLDER. "DP" stands for Decision Problem.
 * Niccolò Carrivale + CREAM
 * Input: 
 * Q_1, a quandle.
 * Q_2, a quandle.
 *
 * Output: True, if there exists a congruence p such that Q_1/p is isomorphic to Q_2; False, otherwise.
 */
intrinsic QuotientQuandleDP(Q_1 :: Qndl, Q_2 :: Qndl) -> BoolElt
{ Solves the Decision Problem: is Q_2 a quotient quandle of Q_1? }
    
    F := QuandleMatrix(Q_1);
    M := QuandleMatrix(Q_2);
    
    return QuotientQuandleDP(F,M);
end intrinsic;

/*
 * NOTE THE NAME OF THIS FUNCTION MIGHT *NOT* BE APPROPRIATE. CONSIDER IT A PLACEHOLDER.
 * Niccolò Carrivale + CREAM 
 * Input: Let A = <X = {1, 2, ..., n}, F> be a quandle, for some n in N.
 * Let B = <Y = {1, 2, ..., m}, M> be a quandle, for some m in N.
 * Let n >= m.
 *
 *  F : The binary operation on X represented by sequences of sequences.
 *  M : The binary operation on Y represented by sequences of sequences.
 *
 * Output: True, if there exists a congruence p such that A/p is isomorphic to B; False, otherwise.
 */
intrinsic QuotientQuandleDP(Q_1 :: SeqEnum[SeqEnum[RngIntElt]], Q_2 :: SeqEnum[SeqEnum[RngIntElt]]) -> BoolElt
{ Solves the Decision Problem: is Q_2 a quotient quandle of Q_1? }
    
    if #Q_1 gt #Q_2 then 
        return false;
    end if;

    F := UnarifyAlgebra([Q_1]);
    congruencesA := AllCongruences(F);


    for congruence in congruencesA do
        if #Q_1 eq NumberOfBlocks then
            QQuandle := QuotientQuandle(Q_1, congruence);
            isomorphism := Monomorphism(QuandleMatrix(QQuandle),Q_2);
            if isomorphism ne [] then 
                return true;
            end if;
        end if;
    end for;
    return false;
end intrinsic;



/*
 * CREAM + Niccolò Carrivale
 * Input: Let Q = (X, *) be a quandle, for some n in N.
 * F : The multiplication table of Q, represented by a square sequence of sequences. 
 * subQ : A subset of X closed under *.
 * element : An element of X.
 *
 *
 * Output: Let S be a subset of R. Let us defined a * S = { a * s : s in S } and S * a = { s * a : s in S}, for a in R. 
 * The function returns (S * a) U (a * S)
 */
intrinsic SubuniverseElement(F :: SeqEnum[SeqEnum[RngIntElt]], subQ :: SetEnum[RngIntElt], element :: RngIntElt) -> SetEnum[RngIntElt]
{ Expands subQ by with element, ensuring it is still closed under the operation of the quandle }
    
    Elements := { element };

    subQExpanded := subQ;

    No_Elements := 1;


    while No_Elements gt 0 do
        

        current := 0;

        ExtractRep(~Elements, ~current);

        ElementsExpanded := { F[current][current] };
    
        for subElement in subQExpanded do
            Include(~ElementsExpanded, F[current][subElement]);
            Include(~ElementsExpanded, F[subElement][current] );
        end for;
    
        Include(~subQExpanded, current);
        
        Elements := Elements join (ElementsExpanded diff subQExpanded) ;
        No_Elements := #Elements;
        if (#subQExpanded + No_Elements) eq #F then 
            subQExpanded := { 1 .. #F };
            No_Elements := 0;
        end if;
    end while; 

   
    return subQExpanded;
end intrinsic;

/*
 * CREAM + Niccolò Carrivale
 * Input: Q, a quandle.
 *
 * Output: Computes all the subuniverses of quandle Q.
 */
intrinsic Subuniverses(Q :: Qndl) -> SetIndx[SetIndx[RngIntElt]]
{ Returns all the subuniverses of quandle Q }
    
    return Subuniverses(QuandleMatrix(Q));

end intrinsic;



/*
 * CREAM + Niccolò Carrivale
 * Input: Let Q be a quandle, for some n in N.
 * F : The multiplication table of Q, represented by a square sequence of sequences. 
 *
 * Output: Computes all the subuniverses of the quandle Q, represented by the square sequence of sequences F.
 */
intrinsic Subuniverses(F :: SeqEnum[SeqEnum[RngIntElt]]) -> SetIndx[SetEnum[RngIntElt]]
{ Returns all the subuniverses of quandle Q }
    AutQ := AutQuandle(F);
    BaseSubalgebras := {@ @};
    SubalgebrasExpanded := {@ @};
    for index := 1 to #F do
        BaseSubalgebrasElement := {@ @};
        PreviousRoundSubalgebras := index eq 1 select {@ { } @} else SubalgebrasExpanded[index-1];

        for currentSubalgebra in PreviousRoundSubalgebras do
            Elements := {1 .. #F} diff currentSubalgebra;
            while #Elements ne 0 do
                element := 0;
                ExtractRep(~Elements,~element);
                generatedSubuniverse := SubuniverseElement(F, currentSubalgebra, element);
                Include(~BaseSubalgebrasElement, generatedSubuniverse);
                Elements := Elements diff (element^AutQ);
            end while;
        end for;

        SubalgebrasExpandedElement := {@ @};
        for Subalgebra in BaseSubalgebrasElement do
            SubalgebrasExpandedElement := (SubalgebrasExpandedElement) join {@ x : x in (Subalgebra^AutQ) @};
        end for;
        
        Include(~SubalgebrasExpanded, SubalgebrasExpandedElement);
        Include(~BaseSubalgebras, BaseSubalgebrasElement);

        if #BaseSubalgebrasElement eq 1 and #BaseSubalgebrasElement[1] eq #F then 
            break;
        end if;
    end for;
  
    Subalgebras := &join SubalgebrasExpanded;

    return Subalgebras;
end intrinsic;