
// Definition of the type for (general) Quandles
declare type Qndl;

// Definition of the attributes of a Quandle
declare attributes Qndl: Set, Operation;


/*
 * Input: a Quandle T
 *
 * Output: Integral Quandle Matrix
 */
intrinsic QuandleMatrix(T :: Qndl) -> SeqEnum[SeqEnum[RngIntElt]]
{ It generates the integral quandle matrix as defined in MATRICES AND FINITE QUANDLES by BENITA HO and SAM NELSON }
	return [ [T`Operation(<x,y>) : y in T`Set ]: x in T`Set ];
end intrinsic;

// Definition of the type for Trivial Quandles
declare type TrvQndl: Qndl;

intrinsic Print(Q :: Qndl)
{ Print Q }
	printf "%o", QuandleMatrix(Q);
end intrinsic;

/*
 * Input: 
 * 	A set X,  
 * 	An operation M
 *
 * Output: A Quandle with underlying set X and operation M
 */
intrinsic Quandle(X :: SetEnum[RngIntElt], M :: Map[SetCart, SeqEnum[RngIntElt]]) -> Qndl
{ It generates the Trivial Quandle with underlying set X }
	
	// Creates the Quandle
    T := New(Qndl);
	
	// Sets X as the underlying set of the Quandle
    T`Set := Sort(Setseq(X));

	// Defines the operation of the Trivial Quandle
    T`Operation := M;

	
	// If, for any reason, the provided set and this operation do not form a quandle, the function will not return anything.
	require isQuandle(QuandleMatrix(T), T`Set): "The provided set does not generate a quandle with this associated operation.";
        
	return T;
end intrinsic;


/*
 * Input: A set X
 *
 * Output: The Trivial Quandle with underlying set X
 */
intrinsic TrivialQuandle(X :: SetEnum[RngIntElt]) -> TrvQndl
{ It generates the Trivial Quandle with underlying set X }
	
	// Creates the Quandle
    T := New(TrvQndl);
	
	// Sets X as the underlying set of the Quandle
    T`Set := Sort(Setseq(X));

	// Defines the operation of the Trivial Quandle
    T`Operation := map< car<T`Set,T`Set> -> T`Set | x :-> x[2] >;

		
	// If, for any reason, the provided set and this operation do not form a quandle, the function will not return anything.
	require isQuandle(QuandleMatrix(T), T`Set): "The provided set does not generate a quandle with this associated operation.";
        
	return T;
end intrinsic;

// Definition of the type for Dihedral Quandles
declare type DhdrlQndl: Qndl;


/*
 * Input: A set X
 *
 * Output: The Dihedral Quandle with underlying set X
 */
intrinsic DihedralQuandle(X :: SetEnum[RngIntElt]) -> DhdrlQndl
{ It generates the Dihedral Quandle with underlying set X }

	// Creates the Quandle
    T := New(DhdrlQndl);
	
	// Sets X as the underlying set of the Quandle
    T`Set := Sort(Setseq(X));

	// Defines the operation of the Dihedral Quandle: x * y = ((2x) - y) mod (|X|))
	/*
	 * Let x = (x[1], x[2]) = (a, b) in X * X (where X * X is the Cartesian Product of X and X). 
	 * The additional logic "(((2*a) - b) mod (# X)) eq 0 select (#X) else (((2*a) - b) mod (# X))" says
	 * if ((2*a) - b) mod (# X)) = 0 then return the cardinality of the set which is also expected to be the greatest element of the set
	 * this is correct because 0 = |X|	(mod |X|);
	 * in any other case, we return the regular result.
	 */
    T`Operation := map< car<T`Set,T`Set> -> T`Set | x :-> (((2*x[1]) - x[2]) mod (# T`Set)) eq 0 select (#T`Set) else (((2*x[1]) - x[2]) mod (# T`Set)) >;
		
	// If, for any reason, the provided set and this operation do not form a quandle, the function will not return anything.
	require isQuandle(QuandleMatrix(T), T`Set): "The provided set does not generate a quandle with this associated operation.";
        
    return T;
end intrinsic;

// Definition of the type for Quandles from a matrix
declare type QndlFM: Qndl;

/*
 * Input: 
 * M : the multiplication table of a quandle represented by a square sequence of sequences.
 * expected : a boolean flag indicating whether the function can expect to be working with {1 .. n} for some n in N or not. 
 *
 * Output: A Quandle with underlying set X and operation described by M
 */
intrinsic QuandleFM(M :: SeqEnum[SeqEnum[RngIntElt]], expected :: BoolElt) -> QndlFM
{ A Quandle with underlying set and operation described by M }

	
	
	// Creates the Quandle
    T := New(QndlFM);
	
	/*
	 * Sets X as the underlying set of the Quandle -
	 *  This is possible because, by quandle axiom 2, any row of a quandle multiplication table must be a permutation of the underlying set
	 */
	T`Set := Sort(M[1]);

	require isQuandle(M, T`Set): "This is not an integral quandle matrix.";

	for index_1 := 1 to #T`Set do
		for index_2 := index_1+1 to #T`Set do
			error if T`Set[index_1] eq T`Set[index_2], "This multiplication table does not represent a quandle";
		end for;
	end for;

	/*
	 * Defines the operation of the Quandle
	 */
	T`Operation := MappifyOperation(T`Set, M, expected);
        
	return T;
end intrinsic;


/*
 * Input: 
 * M : A square sequence of sequences 
 * uSet : the (labels of the) underlying set as a sorted sequence
 *
 * Output: True if m_ii = i where i is the i-th label of the sorted underlying set, False otherwise.
 */
intrinsic checkDiagonal(M :: SeqEnum[SeqEnum[RngIntElt]], uSet : SeqEnum) -> BoolElt
{ It checks whether the table/matrix meets the first requirement of a quandle(for all x in S, x * x = x) }
	
	require #uSet eq #M : "The cardinality of the provided underlying set is not the same as the number of rows in M";
	
	
	for index := 1 to (#M) do

		require #M[index] eq #M : "This is not a square sequence of sequences.";

		/*
		 * Checks whether m_ii =  where i is the i-th element of uSet; if not, it returns False. 
		 * This is stronger than the quandle axiom for idempotency but ensures an integral quandle matrix. 
		 */
		if M[index,index] ne uSet[index] then 
			return false;
		end if;	
	end for;

	return true;
end intrinsic;



/*
 * Input: 
 * M : A square sequence of sequences 
 * uSet : The underlying set of M as a sequence
 *
 * Output: True if for each row R of M, each entry x in R appears exactly one, False otherwise.
 */
intrinsic checkRows(M :: SeqEnum[SeqEnum[RngIntElt]], uSet : SeqEnum) -> BoolElt
{ It checks whether the table/matrix meets the second requirement(the map px : S -> S    y :-> x * y is a bijection) }

	// we can skip of the checks here because checkRows is supposed to be used after checkDiagonal

	// Keeps track of the appeared elements
	check := true;

	for row := 1 to (#M) do 
		/*
		 * since checkDiagonal "forces" each row of M to have the same cardinality of uSet, 
		 * if any element of uSet appears in M[row], we have a permutation.
		 * This is because, in QuandleFM we check that uSet has no duplicates. 
		 */
		check := check and IsSubsequence(uSet, M[row]: Kind := "Setwise");
	end for;
	return check;
end intrinsic;

/*
 * Input: 
 * M : A square sequence of sequences 
 * uSet : the underlying set of M as a sorted sequence
 * 
 * 
 *
 * Output: Let n be the number of rows(and columns) of M. True if for all x,y,z in {1,2, .. ,n} M[x, M[y, z]] = M[M[x,y], M[x,z]], False otherwise.
 */
intrinsic checkDistributivity(M :: SeqEnum[SeqEnum[RngIntElt]], uSet : SeqEnum) -> BoolElt
{ It checks whether the table/matrix meets the third requirement(For all elements x, y, z in S: x * (y * z) = (x * y) * (x * z)) }
	expected := uSet eq [1..#M];
	for x := 1 to (#M) do    
		for y := 1 to (#M) do
			for z := 1 to (#M) do
				/*
				 * If there exist three elements x, y, z in S such that x * (y * z) /= (x * y) * (x * z)
				 * the second axiom does not hold, hence it returns False;
				 */
				if expected then 
					if (M[x, M[y, z]] ne M[M[x, y], M[x, z]]) then
						return false;
					end if;
				else 
					if (Index(uSet, M[x, Index(uSet, M[y, z])]) ne Index(uSet,M[Index(uSet, M[x, y]), Index(uSet, M[x, z])])) then
						return false;
					end if;
				end if;


			end for;        
		end for;                
	end for;

	return true;
end intrinsic;

/*
 * Input: 
 * A square sequence of sequences M
 * uSet : the underlying set of M as a sorted sequence 
 *
 * Output: True if M represents a Rack, false otherwise.
 */
intrinsic isRack(M :: SeqEnum[SeqEnum[RngIntElt]], uSet :: SeqEnum) -> BoolElt
{ It checks whether the sequence of sequences M represents a Rack }
	// It checks the second and third axiom
	axiom2 := checkRows(M, uSet);
	axiom3 := checkDistributivity(M, uSet);

    require axiom2 : "Axiom 2 does not hold.";
    require axiom3 : "Axiom 3 does not hold.";
                       
	return axiom2 and axiom3;
end intrinsic;

/*
 * Input: 
 * M : A square sequence of sequences M
 * uSet : the underlying set of M as a sorted sequence
 * 
 *
 * Output: True if M represents a Quandle, false otherwise.
 */
intrinsic isQuandle(M :: SeqEnum[SeqEnum[RngIntElt]], uSet :: SeqEnum) -> BoolElt
{ It checks whether the sequence of sequences M represents a Quandle }
	// It checks the three Quandle axioms
	axiom1 := checkDiagonal(M, uSet);
	require axiom1 : "Axiom 1 does not hold.";

	axiom23 :=  isRack(M, uSet);

	return axiom1 and axiom23;
end intrinsic;








