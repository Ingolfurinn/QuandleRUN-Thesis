
/*
 * Input: 
 *	c, cardinality of the desired quandle 
 * 	n, index of the desired quandle with cardinality c 
 *
 * Output: Integral quandle matrix(as a square sequence of sequences) of the requested quandle
 */
intrinsic QueryQuandle(c :: RngIntElt, n :: RngIntElt) -> SeqEnum[SeqEnum[RngIntElt]]
{ Returns the integral quandle matrix of the n-th Quandle with cardinality c }
	
	// The terminal command to run the utility 'Reader.py' is constructed.
    command := "python3 Reader.py " * (IntegerToString(c) * (" " * IntegerToString(n)));
    
    str_ := Pipe(command, "");
       
    // The matrix is obtained as a string. Spaces, square backets, tab and new line characters are removed.
    entries := Split(str_, "[], \t\n");

    // Safety check that the obtained matrix is actually a square. The database seems to be safe but there could be errors in 'SmallQuandles.m' or 'Reader.py'.
    _, cardinality := IsSquare(#entries);
    require (cardinality ge 1) : "Something is wrong with the cardinality of this matrix.";

    matrix := [ ];
    for index_1 := 1 to cardinality do
        Lx := [ ];

        for index_2 := 1 to cardinality do
        // The sequences of the entries of the matrix are constructed by turning the characters into integers.
            Append(~Lx, StringToInteger(entries[index_2+cardinality*(index_1-1)]));
        end for;
            Append(~matrix, Lx);
    end for;
    
    
    
    // The matrix returned.
    return matrix;
    

end intrinsic;

