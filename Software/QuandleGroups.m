// Definition of the type for Conjugation Quandles
declare type GrpQndl: Qndl;

// Definition of the type for Conjugation Quandles
declare type ConjQndl: GrpQndl;

// Definition of the type for Core Quandles
declare type CoreQndl: GrpQndl;

// Definition of the type for Coset Quandles
declare type HomQndl: GrpQndl;

// Definition of extra attributes for Quandles arisen from a Group
declare attributes GrpQndl: Group;

// Definition of extra attributes for Quandles arisen from a Group, a subgroup and an automorphism
declare attributes HomQndl: Subgroup, Aut_element;

/*
 * Input: 
 * A group G,
 * An integer n.
 *
 *
 * Output: The n-fold Conjugation quandle.
 */
intrinsic ConjugationQuandle(G :: Grp, n :: RngIntElt) -> ConjQndl
{ It generates the n-fold Conjugation quandle of group G }

    // Numbering Map accepts only groups in GrpPerm, GrpMat, GrpPC, GrpAb; thus we need we to make sure we are dealing with one. 
    require Type(G) in [GrpPerm, GrpMat, GrpPC, GrpAb] : "Group in the wrong category. ";

	// Creates the Quandle
    T := New(ConjQndl);
	
    // Sets G as the group from which the Quandle arose
    T`Group := G;

    // A bijective function from the underlying set of G to { 1, 2, ... , Order(G)}.
    phi := NumberingMap(G);

	// Sets X as the underlying set of the Quandle, where X is the underlying set of the group G.
    T`Set := [element : element in G];

    if Type(G) eq GrpAb then
        T`Operation := map< car<T`Set,T`Set> -> [1 .. Order(G)] | x :-> phi(x[1]*n + x[2] + x[1] * -n) >;
    else
        T`Operation := map< car<T`Set,T`Set> -> [1 .. Order(G)]  | x :-> phi(x[1]^n * x[2] * x[1]^-n) >;
    end if;
    
		
	// If, for any reason, the provided set and this operation do not form a quandle, the function will not return anything.
	require isQuandle(QuandleMatrix(T)): "The provided set does not generate a quandle with this associated operation.";
        
    return T;
end intrinsic;


/*
 * Input: a group G
 *
 *
 * Output: The Core quandle.
 */
intrinsic CoreQuandle(G :: Grp) -> CoreQndl
{ It generates the Core quandle of group G }

    // Numbering Map accepts only groups in GrpPerm, GrpMat, GrpPC, GrpAb; thus we need we to make sure we are dealing with one. 
    require Type(G) in [GrpPerm, GrpMat, GrpPC, GrpAb] : "Group in the wrong category. ";

	// Creates the Quandle
    T := New(CoreQndl);
	
    // Sets G as the group from which the Quandle arose
    T`Group := G;

    // A bijective function from the underlying set of G to { 1, 2, ... , Order(G)}.
    phi := NumberingMap(G);

	// Sets X as the underlying set of the Quandle, where X is the underlying set of the group G.
    T`Set := [element : element in G];

	// Defines the operation of the Core Quandle: x * y = yx^-1y

    if Type(G) eq GrpAb then
        T`Operation := map< car<T`Set,T`Set> -> [1 .. Order(G)]  | x :-> phi(x[1] + x[2] * -1 + x[1]) >;
    else
        T`Operation := map< car<T`Set,T`Set> -> [1 .. Order(G)]  | x :-> phi(x[1] * x[2]^-1 * x[1])  >;
    end if;
    
		
	// If, for any reason, the provided set and this operation do not form a quandle, the function will not return anything.
	require isQuandle(QuandleMatrix(T)): "The provided set does not generate a quandle with this associated operation.";
        
    return T;
end intrinsic;




/*
 * Input: 
 *  A group G,
 *  f in Aut(G)
 *
 * Output: The homogeoneous quandle Q_Hom(G,f).
 */
intrinsic HomogeneousQuandle(G :: Grp, f :: GrpAutoElt) -> HomQndl
{ It generates the homogeoneous quandle Q_Hom(G,f) as described in ON CONNECTED QUANDLES OF PRIME ORDER by GIULIANO BIANCO and MARCO BONATTO }

    // Numbering Map accepts only groups with category in {GrpPerm, GrpMat, GrpPC, GrpAb}; thus we need we to make sure we are dealing with one. 
    require Type(G) in [GrpPerm, GrpMat, GrpPC, GrpAb] : "Group in the wrong category. ";

    // Verifies that f is an automorphism of G: f in AutomorphismGroup(G)
    require f(G) eq G: "f is not an element of Aut(G). ";

	// Creates the Quandle
    T := New(HomQndl);
	
    // Sets G as the group from which the Quandle arose
    T`Group := G;

    // Sets H as the subgroup of G from which the Quandle arose. 
    // (G.0) is the neutral element. This is just bookkeeping - the subgroup H is not important in this case.
    T`Subgroup := sub< G | G.0 >;

    // Sets f as the automorphism of G from which the Quandle arose
    T`Aut_element := f;

    // A bijective function from the underlying set of G to { 1, 2, ... , Order(G)}.
    phi := NumberingMap(G);

	// Sets X as the underlying set of the Quandle, where X is the underlying set of the group G.
    T`Set := [element : element in G];

	// Defines the operation of the Homogeneous Quandle: x * y = xf(x^-1y)

    if Type(G) eq GrpAb then
        T`Operation := map< car<T`Set,T`Set> -> [1 .. Order(G)]  | x :-> phi(x[1] + f(x[1]*-1 + x[2])) >;
    else
        T`Operation := map< car<T`Set,T`Set> -> [1 .. Order(G)]  | x :-> phi(x[1] * f(x[1]^-1 * x[2]))  >;
    end if;
    
		
	// If, for any reason, the provided set and this operation do not form a quandle, the function will not return anything.
	require isQuandle(QuandleMatrix(T)): "The provided set does not generate a quandle with this associated operation.";
        
    return T;
end intrinsic;


/*
 * Input: 
 *  A group G,
 *  A subgroup of H whose elements are fixed by f,
 *  f in Aut(G)
 *
 * Output: The coset quandle Q_Hom(G,f).
 */
intrinsic CosetQuandle(G :: Grp, H :: Grp, f :: GrpAutoElt) -> HomQndl
{ It generates the coset quandle Q_Hom(G,H,f) as described in ON CONNECTED QUANDLES OF PRIME ORDER by GIULIANO BIANCO and MARCO BONATTO }

    // Numbering Map accepts only groups with category in {GrpPerm, GrpMat, GrpPC, GrpAb}; thus we need we to make sure we are dealing with one. 
    // Computing Left and/or Right cosets for Abelian Quandles does not seems to be implemented in MAGMA. 
    // Once, I find a way to compute those coset quandles arising from abelian groups will be supported. 
    require Type(G) in [ GrpPerm, GrpMat, GrpPC ] : "Group in the wrong category. ";

    // Verifies that f is an automorphism of G: f in AutomorphismGroup(G)
    require f(G) eq G: "f is not an element of Aut(G). ";

    // Verifies that f is a subgroup of G
    require H subset G : "H is not a subgroup of G.";

    for x in H do 
        error if f(x) ne x, "Not all elements of H are fixed by f. ";
    end for;

	// Creates the Quandle
    T := New(HomQndl);
	
    // Sets G as the group from which the Quandle arose
    T`Group := G;

    // Sets H as the subgroup of G from which the Quandle arose
    T`Subgroup := H;

    // Sets f as the automorphism of G from which the Quandle arose
    T`Aut_element := f;

    Elem_and_coset := [ <x, x * H> : x in G ];
    
    // For some reason the MAGMA function Index(Sequence, Element) does not work when Sequence := Elem_and_coset, so I am defining my own function. 
    index_for_coset := function(sequence, element)
                            for index in [1 .. # sequence] do
                                if (sequence[index][2] eq element[2]) then
                                    return index;
                                end if;
                            end for;
                            return 0;
                         end function;
    
    // Furthermore, we cannot use Seqset to turn 'Elem_and_coset' into a set, so we need to do some manual cleaning
    tmp_Elem_and_coset := [];
    for element in Elem_and_coset do
        if index_for_coset(tmp_Elem_and_coset, element) eq 0 then
            Append(~tmp_Elem_and_coset, element);
        end if;
    end for;
    Elem_and_coset := tmp_Elem_and_coset;

    T`Set := [ x[1] : x in Elem_and_coset ];

    // Defines the operation of the coset Quandle: xH * yH = xf(x^-1y)H
    T`Operation := map< car<T`Set,T`Set> -> [1 .. # Elem_and_coset ] | x :->  index_for_coset(Elem_and_coset, <x[1],  (x[1] * f(x[1]^-1 * x[2])) * H >) >;
   
    
	// If, for any reason, the provided set and this operation do not form a quandle, the function will not return anything.
	require isQuandle(QuandleMatrix(T)): "The provided set does not generate a quandle with this associated operation.";
        
    return T;
end intrinsic;