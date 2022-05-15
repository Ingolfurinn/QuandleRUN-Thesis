// This is mostly a MAGMA translation of CREAM (possibly adapted to work specifically/only on Quandles) presented in 
// [CRP1] CREAM: A PACKAGE TO COMPUTE [AUTO, ENDO, ISO, MONO, EPI]-MORPHISMS, CONGRUENCES, DIVISORS AND MORE FORE ALGEBRA OF TYPE (2^n, 1^n)

// I added some extra functions to make life easier.

// Contrary to COMPUTING CONGRUENCES EFFICIENTLY by RALPH FREESE, the root of a tree(block of a partition) here is the minimum element.

/* 
 * N. Carrivale
 * Input: M, A binary operation on some subset of N with cardinality n, represented by a square sequence of sequences.
 * 
 *
 * Output: It returns a sequence containing all the distinct unary operations on X induced by the binary operation M.
 */
intrinsic UnarifyOperation(M :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SeqEnum[RngIntElt]]
{ Returns a sequence containing all the distinct unary operations on X induced by the binary operation. }

    /*
     * The algorithm described by Ralph Freese in COMPUTING CONGRUENCES EFFICIENTLY
     * only works with unary algebras, that is, algebras with only unary operations.
     *
     * Hence we need to convert binary operation to 2n unary operations where n is the cardinality of X.
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
    
   
    X := Sort(M[1]);

   
    UnaryOperations := [];
    for index_1 := 1 to #M do

        row := [];
        column := [];

        for index_2 := 1 to #M do
            

            try 
                resultrow := M[index_1, index_2];
                resultcolumn := M[index_2, index_1];
                error if resultrow notin X, "This multiplication table does not represent an operation.";
                error if resultcolumn notin X, "This multiplication table does not represent an operation.";
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
 * Input: Let A = <X, F> be a unary or "unarified" binary algebra.
 * X : the (labels of the) underlying set of A as a sorted sequence.
 * F : A sequence of unary operations on X represented by a sequence of sequences.
 * GeneratingPair : A pair <a, b> with a, b in X.
 * expected: a boolean flag indicating whether X is the expected set with n elements({1..n}) or not. 
 * 
 *
 * Output: The principal congruence generated by a and b in A.
 */
intrinsic PrincipalCongruence(X :: SeqEnum[RngIntElt], F :: SeqEnum[SeqEnum[RngIntElt]], GeneratingPair :: Tup, expected :: BoolElt) -> SeqEnum[RngIntElt]
{ It returns the principal congruence generated by a and b in A }
    Pairs := [ GeneratingPair ];

    congruence := [ -1 : x in F[1] ];

    if expected then 
        congruence := JoinBlocks(GeneratingPair[1], GeneratingPair[2], congruence); 
    else
        congruence := JoinBlocks(Index(X,GeneratingPair[1]), Index(X,GeneratingPair[2]), congruence); 
    end if;
    
    while not IsEmpty(Pairs) do
        Pair := Pairs[1];
        Remove(~Pairs, 1);
        for f in F do
            if expected then 
                root1, congruence := RootBlock(f[Pair[1]], congruence);
                root2, congruence := RootBlock(f[Pair[2]], congruence);
            else 
                root1, congruence := RootBlock(Index(X, f[Index(X, Pair[1])]), congruence);
                root2, congruence := RootBlock(Index(X, f[Index(X, Pair[2])]), congruence);
            end if;
            if root1 ne root2 then 
                congruence := JoinBlocks(root1, root2, congruence);
                Append(~Pairs, <X[root1], X[root2]>);
            end if;

        end for;
    end while;
    return NormalisePartition(congruence);
end intrinsic;




/*
 * CREAM
 * Input: Let A = <X, F> be a unary or "unarified" algebra.
 *  F : A sequence of unary or "unarified" operations on X represented by a sequence of sequences.
 *
 *
 * Output: All the principal congruences of A.
 */
intrinsic AllPrincipalCongruences(F :: SeqEnum[SeqEnum[RngIntElt]]) -> SetIndx[SeqEnum[RngIntElt]]
{ It returns all the principal congruences of A }
   congruences := {@ @};

   uSet := Sort(F[1]);
   expected := IsSubsequence([1..#F], uSet: Kind := "Setwise");

   for index_1 := 1 to ((#F[1]) - 1) do
        for index_2 := (index_1 + 1) to #F[1]  do
            congruence := PrincipalCongruence(uSet, F, <uSet[index_1], uSet[index_2]>, expected);

            Include(~congruences, congruence);
            
        end for;
    end for;
    return congruences;
end intrinsic;


/*
 * CREAM
 * Input: Let A = <X, F> be a unary or "unarified" binary algebra.
 *  F : A sequence of unary or "unarified" operations on X represented by a sequence of sequences.
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

    expected := IsSubsequence([1..#F`Set], F`Set: Kind := "Setwise");
    RSQM := MappifyOperation(F`Set, QuandleMatrix(F), expected);
    candidates := InvariantPartition(InvariantMap(F`Set,RSQM));

        
    return EfficientGeneratingSet(F`Set, RSQM, candidates);
   
end intrinsic;




/*
 * CREAM
 * Input: Let A = <X, F> be binary algebra with a single operation.
 *  uSet : X as a sorted sequence. 
 *  F : The binary operation on X represented by a MAGMA Map.
 *  candidates: a partition of X.
 *
 *
 * Output: A generating set for A
 */
intrinsic EfficientGeneratingSet(uSet :: SeqEnum, F :: Map[SetCart, SeqEnum[RngIntElt]], candidates :: SeqEnum[SeqEnum[RngIntElt]]) -> SetIndx[RngIntElt]
{ It returns a generating set for A }

    submagma := {};
    generator := { };
    
        
    while #submagma ne #uSet do
        most := <0,0,{}>;
        for index_block := 1 to #candidates do
            for index_element := 1 to #candidates[index_block] do
                generated := generatedSet(generator join { uSet[candidates[index_block][index_element]] }, { }, F);
                if #generated gt #most[3] then 
                     most := <index_block,index_element,generated>;
                end if;
            end for;
        end for;
        Include(~generator, uSet[candidates[most[1]][most[2]]]);
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
 * Input: Let A = <X, F> be binary algebra with a single operation.
 *  uSet : X as a sorted sequence of n elements. 
 *  F : The binary operation on X represented by a MAGMA Map.
 *
 *
 * Output: A sequence S with n elements S[i] = [a, b, c, d, e] where 
 * a is the value of invariant 2 for the i-th element, 
 * b is the value of invariant 3 for the i-th element, 
 * c is the value of invariant 6 for the i-th element, and 
 * d is the value of invariant 11 for the i-th element.
 * e is the value of invariant 17 for the i-th element.
 */
intrinsic InvariantMap(uSet :: SeqEnum, F :: Map[SetCart, SeqEnum[RngIntElt]]) -> SeqEnum[SeqEnum[RngIntElt]]
{ Returns the sequence containing the values of invariants 2, 3, 6, 11 and 17 in CR1 for each element of X }

    invariant_vector := [ ];
    partition_ := [];
    
    for index_1 := 1 to #uSet do
        
        invariant_2 := 0;
        invariant_3 := 0;
        invariant_6 := [];
        invariant_11 := 0;
        
        for index_2 := 1 to #uSet do

            result_1 := F(<uSet[index_1],uSet[index_2]>);
            result_2 := F(<uSet[index_2],uSet[index_1]>);


            if result_1 eq uSet[index_2] then 
                invariant_2 := invariant_2 + 1;
            end if;

            if result_2 eq uSet[index_2] then 
                invariant_3 := invariant_3 + 1;
            end if;

            if result_1 eq result_2 then 
                invariant_11 := invariant_11 + 1;
            end if;

            if result_1 notin invariant_6 then 
                Append(~invariant_6, result_1);
            end if;

        end for;

        invariant_vector[index_1] := [ invariant_2, invariant_3, #invariant_6, invariant_11 ];

    end for;

    subs := Subsets(Seqset(uSet), 2);

    for index_1 := 1 to #uSet do

        invariant_17 := [];

        for t in subs do
            t_seq := [ x : x in t];

            a := F(<t_seq[1],t_seq[2]>);
            b := F(<t_seq[2],t_seq[1]>);

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
 * Input: Let A = <X, F> be binary algebra with a single operation.
 *  Invariants : A sequence [x1, x2, ..., xn] inducing an equivalence relation.
 *
 * Output: The partion on {1..n} induced by the sequence 'Invariants'. 
 */
intrinsic InvariantPartition(Invariants :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[SeqEnum[RngIntElt]]
{ The parition induced by the equivalence relation 'Invariants' }
    
    
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
 *  A potential subquandle of M with cardinality n, F, 
 *  A quandle, M.
 *
 *
 * Output: 
 * [], if there is no monomorphism from F to M.
 * [ f(a_1), f(a_2), ..., f(a_n)] where a_i in F, if there is a monomorphism from F to M.
 */
intrinsic Monomorphism(F :: Qndl, M :: Qndl) -> SeqEnum[RngIntElt]
{ Returns, if it exists, a monomorfism from F to M }

    return Monomorphism(QuandleMatrix(F), QuandleMatrix(M));
    
end intrinsic;


/*
 * CREAM + Niccolò Carrivale 
 * Input: Let A = <X, F> be a binary algebra with a single operation, with n elements.
 * Let B = <Y, M> be a binary algebra with a single operation, with m elements.
 * Let n <= m.
 *
 *  F : The binary operation on X represented by a sequence of sequences.
 *  M : The binary operation on Y represented by a sequence of sequences.
 *
 * Output: 
 * [], if there is no monomorphism from F to M.
 * [ f(a_1), f(a_2), ..., f(a_n)] where a_i in F, if there is a monomorphism from F to M.
 */
intrinsic Monomorphism(F :: SeqEnum[SeqEnum[RngIntElt]], M :: SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum[RngIntElt]
{ Returns, if it exists, a monomorfism from A to B }

    if #F gt #M then 
        return [];
    end if;

    uSetF := Sort(F[1]);
    uSetM := Sort(M[1]);
    mapF := MappifyOperation(uSetF, F, IsSubsequence([1..#uSetF], uSetF: Kind := "Setwise"));
    mapM := MappifyOperation(uSetM, M, IsSubsequence([1..#uSetM], uSetM: Kind := "Setwise"));
    FInvMap := InvariantMap(uSetF, mapF);
    MInvMap := InvariantMap(uSetM, mapM);

    // Very small set - often no more than 3 elements 
    FGenSet := Setseq(EfficientGeneratingSet(uSetF,  mapF, InvariantPartition(FInvMap)));
    
    mapsTo := [ [] : x in FGenSet  ];

    for index_M := 1 to #M do
        for index_mapsTo := 1 to #FGenSet do
            
            if FInvMap[Index(uSetF, FGenSet[index_mapsTo])] le MInvMap[index_M] then
                Append(~mapsTo[index_mapsTo],index_M);
            end if;

        end for;
    end for;

    for images in mapsTo do
        if IsEmpty(images) then 
            return [];
        end if;
    end for;

    monomorphism := ExtendMonomorphism(uSetF, mapF, mapM, FGenSet, mapsTo, [ 0 : index in F ]);

    return monomorphism;
    
end intrinsic;




/*
 * CREAM + Niccolò Carrivale - This is a recursive function
 * Input: Let A = <X, F> be a binary algebra with a single operation, with n elements.
 * Let B = <Y, M> be a binary algebra with a single operation, with m elements.
 * Let n <= m.
 *
 *  F : The binary operation on X represented by a sequence of sequences.
 *  M : The binary operation on Y represented by a sequence of sequences.
 *  FGenSet : A generating set for A.
 *  Images : A sequence holding the possible images for the elements of FGenSet.
 *  morphism : A sequence that hold the current status of the morphism under construction such that morphism[i] indicates the image of i under the morphism. 
 *              f[i] = 0 indicates that an image has not yet been defined. 
 *
 * Output: 
 * [], if there is no monomorphism from F to M.
 * [ f(a_1), f(a_2), ..., f(a_n)] where a_i in F, if there is a monomorphism from F to M.
 */
intrinsic ExtendMonomorphism(uSetF :: SeqEnum[RngIntElt], F :: Map[SetCart, SeqEnum[RngIntElt]], M :: Map[SetCart, SeqEnum[RngIntElt]], FGenSet :: SeqEnum[RngIntElt], Images :: SeqEnum[SeqEnum[RngIntElt]], morphism :: SeqEnum[RngIntElt] ) -> SeqEnum[RngIntElt]
{ Returns, if it exists, a monomorfism from A to B }
    
    
    if IsEmpty(FGenSet) then 
        
        OldElements := {};
        
        
        NewElements := { uSetF[y] : y in [1 ..#morphism] | morphism[y] ne 0 };
        
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
                temp_result := F(<a,b>);
                result_in_A := morphism[Index(uSetF, temp_result)];
                result_in_B := M(<morphism[Index(uSetF,a)],morphism[Index(uSetF,b)]>);
                    // Preserves injectivity
                if (result_in_A eq 0) and (result_in_B notin morphism) then 
                    morphism[Index(uSetF,temp_result)] := result_in_B;
                    Include(~Results, temp_result);
                else 
                    // verifies Def2.1* Universal Algebra - Morphism
                    if morphism[Index(uSetF,temp_result)] ne result_in_B then 
                        return [];
                    end if;
                end if;
            end for;

            OldElements := OldElements join NewElements;
            NewElements := Results diff OldElements;
            
        end while;
        return morphism;
    end if;

    preImage := Index(uSetF,FGenSet[ 1 ]);
    Remove(~FGenSet, 1);
   

    // Preserves injectivity
    availableImages := [ y : y in Images[1] | y notin morphism ];
    Remove(~Images, 1);

    for availableImage in availableImages do

        updatedMorphism := morphism;
        updatedMorphism[preImage] := availableImage;

        updatedMorphism := ExtendMonomorphism(uSetF, F, M, FGenSet, Images, updatedMorphism);
        
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

    F := UnarifyOperation(Q_1);
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
 * Output: Let S be a subset of R. Let us define a * S = { a * s : s in S } and S * a = { s * a : s in S}, for a in R. 
 * The function returns (S * a) U (a * S)
 */
intrinsic SubuniverseElement(F :: Map[SetCart, SeqEnum[RngIntElt]], subQ :: SetEnum[RngIntElt], element :: RngIntElt) -> SetEnum[RngIntElt]
{ Expands subQ by element, ensuring it is still closed under the operation of the quandle }
    
    Elements := { element };

    subQExpanded := subQ;

    No_Elements := 1;


    while No_Elements gt 0 do
        

        current := 0;

        ExtractRep(~Elements, ~current);

        ElementsExpanded := { F(<current,current>) };
    
        for subElement in subQExpanded do
            Include(~ElementsExpanded, F(<current,subElement>));
            Include(~ElementsExpanded, F(<subElement,current>) );
        end for;
    
        Include(~subQExpanded, current);
        
        Elements := Elements join (ElementsExpanded diff subQExpanded) ;
        No_Elements := #Elements;
        if (#subQExpanded + No_Elements) eq #Codomain(F) then 
            subQExpanded := subQExpanded join Elements;
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
    uSetF := Sort(F[1]);
    mapF := MappifyOperation(uSetF, F, IsSubsequence([1..#uSetF], uSetF: Kind := "Setwise"));
    BaseSubalgebras := {@ @};
    SubalgebrasExpanded := {@ @};
    for index := 1 to #F do
        BaseSubalgebrasElement := {@ @};
        PreviousRoundSubalgebras := index eq 1 select {@ { } @} else SubalgebrasExpanded[index-1];

        for currentSubalgebra in PreviousRoundSubalgebras do
            Elements := Seqset(uSetF) diff currentSubalgebra;
            while #Elements ne 0 do
                element := 0;
                ExtractRep(~Elements,~element);
                generatedSubuniverse := SubuniverseElement(mapF, currentSubalgebra, element);
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