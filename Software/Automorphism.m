
/*
 * Input: 
 *	permutation_sigma, a sequence representing a permutation of some subset [1 .. n] of the Integers.
 *	M, a square Matrix - an integral quandle matrix
 *
 * Output: 
 *	Let s be the permutation represented by permutation_sigma;  for example: permutation_sigma: [3 1 2] means that s(1) = 3, s(2) = 1, s(3) = 2.
 *	Ps, the permutation matrix for the permutation 'permutation_sigma'.
 * 	sigma_M, s(M) - each entry m of M has been replaced by s(m).
 *	Transpose(Ps), it is the transpose of Ps and since Ps is an orthogonal matrix, Transpose(Ps) is also the inverse of Ps. 
 */
intrinsic getPermutationMatrices(permutation_sigma :: SeqEnum[RngIntElt], M :: AlgMatElt[RngInt]) -> AlgMatElt[RngInt], AlgMatElt[RngInt], AlgMatElt[RngInt]
{ Given a matrix and a permutation of some subset [1 .. n] of the Integers, it returns a 3-tuple containing the corresponding permutation matrix, its inverse and the matrix after applying the provided permutation }
	sigma_M := M;
	for row := 1 to Nrows(M) do
		for column := 1 to Ncols(M) do
			// Replaces each entry m of M by its image under the permutation and store the result in sigma_M
			sigma_M[row, column] := permutation_sigma[M[row,column]];
		end for;
	end for;
	
	// Computes the permutation matrix corresponding to the provided permutation
    Ps := PermutationMatrix(Integers(), permutation_sigma);
    return Ps, sigma_M, Transpose(Ps);
end intrinsic;


			

/*
 * Input: A square matrix M, representing a quandle.
 *
 * Output: The underlying set of the automorphism group of M
 */
intrinsic Aut_set(M :: AlgMatElt[RngInt], permutations :: GrpPerm) -> SetEnum[SeqEnum[RngIntElt]]
{ Finds the underlying set of the automorphism group of M }	
	Aut := {};
	
	for element in permutations do
		sigma := Eltseq(element);
		Ps, sigma_M, TPs := getPermutationMatrices(sigma,M);
	
		/*
		 * Left multiplication by TPs(the inverse of the permutation matrix Ps reorders the rows of the matrix)
		 * Left multiplication by Ps(the permutation matrix reorders the columns of the matrix)
		 * sigma_M is the sigma(M)
		 */
		Prtd := TPs * sigma_M * Ps;
		
		// Prtd is isomorphic to M but here it is verified whether M was mapped to itself and if so, the permutation is added to the underlying set of Aut(M).
		if Prtd eq M then
			Include(~Aut, sigma);
		end if;
	end for;
	return Aut;
end intrinsic;



/*
 * Input: A square sequence of sequences M, representing a quandle.
 *
 * Output: The automorphism group of M
 */
intrinsic AutQuandle(M :: SeqEnum[SeqEnum[RngIntElt]]) -> GrpPerm
{ Finds the automorphism group of M }

	permutations := Normaliser(Sym(#M),Inn(M));
	
	// Obtains the set of automorphisms	
	Aut_set := Aut_set(Matrix(#M, #M, M), permutations);
	
	// Creates the symmetric group for n = Number of rows of M, because it expects that the underlying set of the quandle Q represented by the integral quandle matrix M is {1, 2, ..., n}.
	S_X := Sym(#M);

	// Initialises an empty list 
	Sym_elements := [];

	for automorphism in Aut_set do
		// Transforms each permutation into an element of the symmetric group and add it to the list
		Append(~Sym_elements, S_X ! automorphism);
	end for;
	
	// Generates the Permutation Group with the permutations found above as generators.
	return sub< S_X | Sym_elements >;
end intrinsic;


/*
 * Input: A square sequence of sequences M, representing a quandle.
 *
 * Output: The inner automorphism group of M.
 */
intrinsic Inn(M :: SeqEnum[SeqEnum[RngIntElt]]) -> GrpPerm
{ Finds the inner automorphism group of M }
	
	

	// Creates the symmetric group for n = Number of rows of M, because it expects that the underlying set of the quandle Q represented by the integral quandle matrix M is {1, 2, ..., n}.
	S_X := Sym(#M);
	
	// Initialises an empty list 
	Sym_elements := [];
	

	for permutation in M do
		// Transforms each permutation(Lx(X), where X is the underlying set of the quandle) into an element of the symmetric group and add it to the list
		Append(~Sym_elements, S_X ! permutation);
	end for;
	
	// Generates the Permutation Group with the permutations found above as generators.
	return sub< S_X | Sym_elements >;
end intrinsic;




/*
 * Input: A square square sequence of sequence M, representing a quandle.
 *
 * Output: Np, the number of standard form integral quandle matrices in the p(ermutation)-equivalence class of the quandle represented by M
 */
intrinsic Np(M :: SeqEnum[SeqEnum[RngIntElt]]) -> RngIntElt
{ It returns the number of standard form integral quandle matrices in the p(ermutation)-equivalence class of the quandle represented by M }
	return (Factorial(#M))/(# Aut(M));
end intrinsic;



/*
 * Input: A square sequence of sequences M, representing a quandle.
 *
 * Output: True if the square Matrix is a latin square, false otherwise
 */
intrinsic isLatin(M :: SeqEnum[SeqEnum[RngIntElt]]) -> BoolElt
{ Checks whether the square matrix M is a latin square or not }
	
	/*
	 * Since MAGMA, as far as I have been able to find out, does not have a function to access the columns of a Matrix but it does have a function to access the rows,
	 * this turns the columns into rows by taking the transpose of the matrix. 
	 * Then it checks that in each row and each column, each value appears exactly once.
	 */	
	
	return checkRows(M) and checkRows(Transpose(M));
end intrinsic;

