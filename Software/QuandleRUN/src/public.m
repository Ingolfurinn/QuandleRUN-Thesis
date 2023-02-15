intrinsic QuandleMatrix(T :: Qndl) -> SeqEnum[SeqEnum[RngIntElt]]
{ It generates the quandle matrix of the Quandle T }
	if ExtendedType(T`Set) eq SetIndx[RngIntElt] then 
		return [ [T`Operation(<x,y>) : y in T`Set ]: x in T`Set ];
	else
		return internal_QuandleMatrix(T);
	end if;
end intrinsic;

intrinsic Print(Q :: Qndl)
{ Prints Q }
	matrix := QuandleMatrix(Q);
	printf "[ \n";
	for x in matrix do
		printf "\t%o\n", x;
	end for;
	printf "]";
end intrinsic;


intrinsic Quandle(X :: SetIndx, M :: Map[SetCart, SetIndx]) -> Qndl
{ It generates the Quandle with underlying set X and operation M}
	require ExtendedType(X) eq ExtendedType(Codomain(M)): "The provided operation is not defined on the provided underlying set.";

    T := New(Qndl);
    T`Set := X;
    T`Operation := M;
	internal_NumberingMap(~T);
	require isQuandle(internal_QuandleMatrix(T), {@ x : x in Codomain(T`_NumberingMap) @}): "The provided set does not generate a quandle with this associated operation.";

	return T;
end intrinsic;

intrinsic TrivialQuandle(X :: SetIndx[RngIntElt]) -> Qndl
{ It generates the Trivial Quandle with underlying set X }
	
    T := New(Qndl);
    T`Set := X;
    T`Operation := map< car<T`Set,T`Set> -> T`Set | x :-> x[2] >;
	internal_NumberingMap(~T);
	require isQuandle(QuandleMatrix(T), T`Set): "The provided set does not generate a quandle with this associated operation.";
        
	return T;
end intrinsic;

intrinsic DihedralQuandle(X :: SetIndx[RngIntElt]) -> Qndl
{ It generates the Dihedral Quandle with underlying set X }
    T := New(Qndl);
    T`Set := X;
    T`Operation := map< car<T`Set,T`Set> -> T`Set | x :-> (((2*x[1]) - x[2]) mod (# T`Set)) eq 0 select (T`Set[#T`Set]) else T`Set[(((2*x[1]) - x[2]) mod (# T`Set))] >;
	internal_NumberingMap(~T);
	require isQuandle(QuandleMatrix(T), T`Set): "The provided set does not generate a quandle with this associated operation.";
        
    return T;
end intrinsic;

intrinsic QuandleFM(M :: SeqEnum[SeqEnum[RngIntElt]], uSet :: SetIndx[RngIntElt]) -> Qndl
{ A Quandle with underlying set uSet and operation described by M }

    require isQuandle(M, {@ M[i,i] : i in [1..#M] @}): "This is not a quandle matrix.";

    T := New(Qndl);
	T`Set := uSet;
    internal_NumberingMap(~T);
	T`Operation := map< car<T`Set,T`Set> -> M[1] | [ <<x,y>, M[T`_NumberingMap(x), T`_NumberingMap(y)]> : x,y in T`Set ] >;

    require isQuandle(QuandleMatrix(T), T`Set): "The provided set does not generate a quandle with this associated operation.";

	return T;
end intrinsic;

intrinsic isQuandle(M :: SeqEnum[SeqEnum[RngIntElt]], uSet :: SetIndx[RngIntElt]) -> BoolElt
{ It checks whether the sequence of sequences M represents a Quandle with underlying set uSet }
	require #uSet eq #M : "The cardinality of the provided underlying set is not the same as the number of rows its Cayley table";
	axiom1 := internal_checkDiagonal(M, uSet);
	require axiom1 : "Axiom 1 (Idemptotency) does not hold.";
	axiom23 :=  internal_isRack(M, uSet);
	return axiom1 and axiom23;
end intrinsic;

intrinsic 'eq' (Q :: Qndl, R :: Qndl) -> BoolElt
{ Returns whether Q and R are the same, internally }
	if #Q`Set ne #R`Set then 
		return false;
	end if;
	return internal_QuandleMatrix(Q) eq internal_QuandleMatrix(R);
end intrinsic;

intrinsic Inn(Q :: Qndl) -> GrpPerm
{ Finds the inner automorphism group of quandle Q }
	return internal_Inn(internal_QuandleMatrix(Q));
end intrinsic;

intrinsic generators(Q :: Qndl) -> SeqEnum[SetIndx[SetEnum[RngIntElt]]]
{ Returns a generating set for the quandle Q }
	return internal_Generators(internal_QuandleMatrix(Q)); 
end intrinsic;

intrinsic AutomorphismGroup(Q :: Qndl) -> GrpPerm
{ Finds the automorphism group of quandle Q }
	return internal_AutomorphismGroup(internal_QuandleMatrix(Q));
end intrinsic;

intrinsic Subquandles(Q :: Qndl) -> SeqEnum[SetEnum[RngIntElt]]
{ Returns all the subquandles of quandle Q }
    
    return internal_Subquandles(internal_QuandleMatrix(Q));
    
end intrinsic;

intrinsic Monomorphism(Q :: Qndl, R :: Qndl) -> GrpPerm
{ Returns a monomorphism from quandle Q to quandle R, if one exists }
	
	return internal_Monomorphism(internal_QuandleMatrix(Q), internal_QuandleMatrix(R));
end intrinsic;

intrinsic Congruences(Q :: Qndl) -> SeqEnum[SetIndx[SetEnum[RngIntElt]]]
{ Returns all the congruences of the quandle Q }
	return internal_Congruences(internal_QuandleMatrix(Q)); 
end intrinsic;

intrinsic ConjugationQuandle(G :: Grp, n :: RngIntElt) -> Qndl
{ It generates the n-fold Conjugation quandle of group G }

    require Type(G) in [GrpPerm, GrpMat, GrpPC, GrpAb] : "Group in the wrong category. ";

    T := New(Qndl);
    T`_NumberingMap := NumberingMap(G);
    T`_NumberingMapInverse := NumberingMap(G)^-1;
    T`Set := G;
    if Type(G) eq GrpAb then
        T`Operation := map< car<T`Set,T`Set> -> T`Set | x :-> (x[1]*n + x[2] + x[1] * -n) >;
    else
        T`Operation := map< car<T`Set,T`Set> -> T`Set  | x :-> (x[1]^n * x[2] * x[1]^-n) >;
    end if;
	require internal_isQuandle(T): "The provided set does not generate a quandle with this associated operation.";
        
    return T;
end intrinsic;

intrinsic CoreQuandle(G :: Grp) -> Qndl
{ It generates the Core quandle of group G }

    require Type(G) in [GrpPerm, GrpMat, GrpPC, GrpAb] : "Group in the wrong category. ";

    T := New(Qndl);
    T`_NumberingMap := NumberingMap(G);
    T`_NumberingMapInverse := NumberingMap(G)^-1;
    T`Set := G;
    if Type(G) eq GrpAb then
        T`Operation := map< car<T`Set,T`Set> -> T`Set  | x :-> (x[1] + x[2] * -1 + x[1]) >;
    else
        T`Operation := map< car<T`Set,T`Set> -> T`Set  | x :-> (x[1] * x[2]^-1 * x[1])  >;
    end if;
	require internal_isQuandle(T): "The provided set does not generate a quandle with this associated operation.";
        
    return T;
end intrinsic;

intrinsic HomogeneousQuandle(G :: Grp, f :: GrpAutoElt) -> Qndl
{ It generates the homogeoneous quandle Q_Hom(G,f) as described in ON CONNECTED QUANDLES OF PRIME ORDER by GIULIANO BIANCO and MARCO BONATTO }

    require Type(G) in [GrpPerm, GrpMat, GrpPC, GrpAb] : "Group in the wrong category. ";
    require f(G) eq G: "f is not an element of Aut(G). ";
    T := New(Qndl);
    T`_NumberingMap := NumberingMap(G);
    T`_NumberingMapInverse := NumberingMap(G)^-1;
    T`Set := G;
    if Type(G) eq GrpAb then
        T`Operation := map< car<T`Set,T`Set> -> T`Set  | x :-> (x[1] + f(x[1]*-1 + x[2])) >;
    else
        T`Operation := map< car<T`Set,T`Set> -> T`Set  | x :-> (x[1] * f(x[1]^-1 * x[2]))  >;
    end if;
	require internal_isQuandle(T): "The provided set does not generate a quandle with this associated operation.";
        
    return T;
end intrinsic;

intrinsic QuotientQuandle(Q :: Qndl, alpha :: SetIndx[SetEnum[RngIntElt]]) -> Qndl
{ It generates the quotient quandle Q/alpha, where alpha is a partition of the labelling induced by a congruence relation }

	error if not internal_hasCompatibilityProperty(internal_QuandleMatrix(Q), alpha), "This equivalence relation does not have the compatibility property.";

    T := New(Qndl);
	T`Set := {@ Rep(block) : block in alpha @};
	find_Rep := function(partition, element)
					for block in partition do
						if element in block then 
							return Rep(block);
						end if;
					end for;
				   end function;

	graph := [ <<x, y>, find_Rep(alpha, Q`_NumberingMap(Q`Operation(<x,y>)))> : x,y in T`Set ];
	T`Operation := map< car<T`Set,T`Set> -> T`Set | graph >;
	internal_NumberingMap(~T);
	require internal_isQuandle(T): "The provided set does not generate a quandle with this associated operation.";
        
	return T;

end intrinsic;

intrinsic isAbelianCongruence(Q :: Qndl, alpha :: SetIndx[SetEnum[RngIntElt]]) -> QuoQndl
{ Checks whether the congruence alpha on quandle Q represented by its induced partition is abelian }

	matrix := internal_QuandleMatrix(Q);

	error if not internal_hasCompatibilityProperty(matrix, alpha), "This equivalence relation does not have the compatibility property.";

	Dis_a := internal_Dis_a(matrix, alpha);
	if not IsAbelian(Dis_a) then 
		return false;
	end if;

	return internal_IsCongruence_semiregular(Dis_a, alpha);
end intrinsic;

intrinsic isCentralCongruence(Q :: Qndl, alpha :: SetIndx[SetEnum[RngIntElt]]) -> QuoQndl
{ Checks whether the congruence alpha on quandle Q represented by its induced partition is central }

	matrix := internal_QuandleMatrix(Q);

	error if not internal_hasCompatibilityProperty(matrix, alpha), "This equivalence relation does not have the compatibility property.";

	Dis_a := internal_Dis_a(matrix, alpha);
	Dis := internal_Dis(matrix);
	if not IsCentral(Dis, Dis_a) then 
		return false;
	end if;

	return internal_IsCongruence_semiregular(Dis, alpha);
end intrinsic;

intrinsic CosetQuandle(G :: Grp, H :: Grp, f :: GrpAutoElt) -> Qndl
{ It generates the coset quandle Q_Hom(G,H,f) as described in ON CONNECTED QUANDLES OF PRIME ORDER by GIULIANO BIANCO and MARCO BONATTO }

    require Type(G) in [ GrpPerm, GrpMat, GrpPC ] : "Group in the wrong category. ";

    require f(G) eq G: "f is not an element of Aut(G). ";

    require H subset G : "H is not a subgroup of G.";

    for x in H do 
        error if f(x) ne x, "Not all elements of H are fixed by f. ";
    end for;

    T := New(Qndl);

    T`Set := {@ { y : y in G | y in  x*H } : x in G @};

    T`Operation := map< car<T`Set,T`Set> -> T`Set | x :->  { y : y in G | y in  (Rep(x[1]) * f(Rep(x[1])^-1 * Rep(x[2])) * H) } >;

    internal_NumberingMap(~T);
	require internal_isQuandle(T): "The provided set does not generate a quandle with this associated operation.";
    return T;
end intrinsic;


intrinsic Dis(Q :: Qndl) -> GrpPerm
{ Finds the displacement group of the quandle Q }
    return internal_Dis(internal_QuandleMatrix(Q));
end intrinsic;

intrinsic Dis_a(Q :: Qndl, alpha :: SetIndx[SetEnum[RngIntElt]]) -> GrpPerm
{ Finds the displacement group of the quandle Q relative to congruence alpha represented by its induced partion of the underlying set of the quandle }
    return internal_Dis_a(internal_QuandleMatrix(Q), alpha);
end intrinsic;

intrinsic Kernel_a(Q :: Qndl, alpha :: SetIndx[SetEnum[RngIntElt]]) -> SetEnum
{ Returns the kernel relative to the congruence alpha represented by its induced partion of the underlying set of the quandle Q }
    return internal_Kernel_a(internal_QuandleMatrix(Q), alpha);	
end intrinsic;
