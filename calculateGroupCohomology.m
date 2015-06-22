(* ::Package:: *)

(* Library to calculate the first group cohomology of surface group representations
 and 1-eigenspaces of actions induced by actions on pi_1

    TODO:
    - port to sage
    - extend to other groups than SU(2)
    - add a test to ensure that a map of pi_1 is actually a map of pi_1
    - add a function which figures out when two reps are conjugate
*)

(* Elementary matrix operations *)
matrixCommutator::notmatrices="At least one of the arguments is not a matrix";
matrixCommutator[a_,b_]:=( 
    If[MatrixQ[a]==False||MatrixQ[b]==False,Message[matrixCommutator::notmatrices];Return[$Failed]];
    Return[a.b.Inverse[a].Inverse[b]]
)

matrixAdjoint::notmatrices="At least one of the arguments is not a matrix";
matrixAdjoint[g_,h_]:=( 
    If[MatrixQ[g]==False||MatrixQ[h]==False,Message[matrixAdjoint::notmatrices];Return[$Failed]];
    Return[g.h.Inverse[g]]
)

matrixProduct[list_List] :=( 
    If[Length[list]==0,Return[IdentityMatrix[2]]];
    Return[Fold[Dot,IdentityMatrix[Length[list[[1]]]],list]];
)

wordToProduct::badword="The first argument should be a list containing integers whose absolute value is no greater than the length of the second argument";
wordToProduct::notmatrices="The second argument should be a list of matrices";
wordToProduct[w_List,l_List]:=( 
    If[MemberQ[Map[IntegerQ[#]&&Abs[#]>0&&Abs[#]<=Length[l]&,w],False],
    Message[wordToProduct::badword];Return[$Failed]];
    If[MemberQ[Map[MatrixQ,l],False],Message[wordToProduct::notmatrices];Return[$Failed]];
    Return[Fold[Dot,IdentityMatrix[Length[l[[1]]]],
        Table[If[i>0,l[[i]],Inverse[l[[-i]]]],{i,w}]
    ]];
)

(*
    Remove from a list of lists all lists containing only zeroes
    
*)
removeZeros[list_List] := 
  DeleteCases[list, row_ /; ! MemberQ[Map[# == 0 &, row], False]];

(*
    Get the intersection of two subspaces in C^n. Input is two lists of vectors.
    Source: http://forums.wolfram.com/mathgroup/archive/2000/Jan/msg00287.html
    Note that the resulting list might contain zero vectors.
*)
intersectionSubspaces[vV_List,wW_List]:=( Module[{mat,nn,len,augmat,redmat,zerorow,relations,multipliers},
    If[vV=={}||wW=={},Return[{}];];
    mat=Join[vV,wW];
    nn=If[Length[vV]!=0,Length[vV[[1]]],Length[wW[[1]]]];
    len=Length[mat];
    augmat=Transpose[Join[Transpose[mat],IdentityMatrix[len]]];
    redmat=RowReduce[augmat];
    zerorow=Table[0,{nn}];
    relations=Select[redmat,(Take[#,nn]==zerorow)&];
    multipliers=Map[Take[#,-Length[wW]]&,relations];
    Return[removeZeros[RowReduce[multipliers.wW]]];
    (*Return[removeZeros[RowReduce[multipliers.wW]]];*)
])

(* Get the word representing the relation in pi_1 of a surface *)
getPiRelation[g_Integer?NonNegative,n_Integer?NonNegative] := (
    Return[Join[
            Flatten[Table[{i,i+1,-i,-i-1},{i,1,2g,2}]]
            ,Table[2g+j,{j,1,n}]
        ]
    ];
)

(* Standard basis vectors of su(2) *)
e[1]:={{0,I},{I,0}};
e[2]:={{0,-1},{1,0}};
e[3]:={{I,0},{0,-I}};

isInSU2::notamatrix="Element is not a matrix";
isInSU2::baddimensions="Element is not 2x2";
isInSU2::baddeterminant="Element does not have determinant 1";
isInSU2::notconjugatetranspose="Element is not in SU(2)";
isInSU2[mat_]:=( 
    If[!MatrixQ[mat],Message[isInSU2::notamatrix];Return[False]];
    If[Map[Length,mat]!={2,2},Message[isInSU2::baddimensions];Return[False]];
    If[Det[mat]!=1,Message[isInSU2::baddeterminant];Return[False]];
    If[mat.ConjugateTranspose[mat]!=IdentityMatrix[2],Message[isInSU2::notconjugatetranspose];Return[False]];
    Return[True];
)

isInsu2::notamatrix="Element is not a matrix";
isInsu2::baddimensions="Element is not 2x2";
isInsu2::badtrace="Element does not have trace 0";
isInsu2::notconjugatetranspose="Element is not in su(2)";
isInsu2[mat_]:=( 
    If[!MatrixQ[mat],Message[isInsu2::notamatrix];Return[False]];
    If[Map[Length,mat]!={2,2},Message[isInsu2::baddimensions];Return[False]];
    If[Tr[mat]!=0,Message[isInsu2::badtrace];Return[False]];
    If[mat!=-ConjugateTranspose[mat],Message[isInSU2::notconjugatetranspose];Return[False]];
    Return[True];
)
su2Coefficients[mat_]:=( 
    If[!isInsu2[mat],Return[$Failed]];
    Return[{Im[mat[[2,1]]],Re[mat[[2,1]]],Im[mat[[1,1]]]}]
)

isRep::badlist="List of matrices should have length 2g+n";
isRep::badargs="Bad list of arguments; please refer to documentation for details";
isRep::notingroup="One or more elements does not belong to the right group";

isRep[g_Integer?NonNegative,n_Integer?NonNegative,rep_List] :=( 
    (* Check that we have the right number of group elements *)
    If[Length[rep]!=2g+n,Message[isRep::badlist];Return[$Failed]];

    (* Ensure that representations is into the right group *)
    If[MemberQ[Map[isInSU2,rep],False],Message[isRep::notingroup];Return[$Failed]];

    (* Check that rep defines a homomorphism *)
    Return[
        matrixProduct[Table[matrixCommutator[rep[[l]],rep[[l+1]]],{l,1,2g,2}]].matrixProduct[Table[rep[[2g+j]],{j,1,n}]]==IdentityMatrix[2]
    ]
)
isRep[g_Integer?NonNegative,rep_List] :=isRep[g,0,rep];
isRep[args___]/;Message[isRep::badargs]=Null;

(* The value of a cocycle u on a commutator [a,b], given u(a), u(b), rho(a) and rho(b) respec. *)
twistedCommun[a_,b_,A_,B_]:=( 
    a+matrixAdjoint[A,b]-matrixAdjoint[A.B.Inverse[A],a]-matrixAdjoint[A.B.Inverse[A].Inverse[B],b]
)

(* The value of a cocycle on the inverse of a generator, given its value $a$ on generators *)
cocycleOnInverse[a_,A_] := -matrixAdjoint[Inverse[A],a];

(* The value of a cocycle on an arbitrary word in the generators, given its value on generators *)
cocycleOnWord::notarep="The representation given is not a representation";
cocycleOnWord::badlength="The length of the list representing the cocycle should be 2g+n";
cocycleOnWord[g_Integer?NonNegative,n_Integer?NonNegative,u_List,rep_List,word_List] :=( 
    If[!isRep[g,n,rep],Message[cocycleOnWord::notarep];Return[$Failed]];
    If[Length[u]!=Length[rep],Message[cocycleOnWord::badlength];Return[$Failed]];
    Return[
        Sum[
            matrixAdjoint[
                If[i==1,IdentityMatrix[2],
                    matrixProduct[Table[
	                If[word[[j]]>0,rep[[word[[j]]]],Inverse[rep[[-word[[j]]]]]]
                        ,{j,1,i-1}]]
                    ]
                    ,If[word[[i]]>0,
                        u[[word[[i]]]],
                        cocycleOnInverse[u[[-word[[i]]]],rep[[-word[[i]]]]]
                    ]
            ]
            ,{i,1,Length[word]}]
    ];
)

(* The value of the relator for a given cocycle at a given representation;
   see p. 82 of my thesis for part of the calculation. *)
   
relator[g_Integer?NonNegative,n_Integer?NonNegative,u_List,rep_List]:=( 
    If[!isRep[g,n,rep],Return[$Failed]];
    If[Length[u]!=Length[rep],Return[$Failed]];
    Return[cocycleOnWord[g,n,u,rep,getPiRelation[g,n]]];
)

(* Finds the parabolic cocycles for a given representation. The output is a matrix whose column vectors form
a basis of Z^1. Coordinates are those obtained by considering an cocycle as an element in su(2)^(2g). *)
findZ1::notarep="The matrices given do not give a representation of pi_1";
findZ1[g_Integer?NonNegative,n_Integer?NonNegative,rep_List] :=( Module[{r,cocycleSatisfied,parabolicMaps,intersection},
    If[!isRep[g,n,rep],Message[findZ1::notarep];Return[$Failed]];
    (* We now construct /all/ maps from pi_1 -> su(2)^{2g+n}. The cocycles are then those
       that map to zero under the linear map defining the cocycle condition for the relator. 
       For their values on the boundary loops, we force the maps constructed to be parabolic.
       *)
    r=Table[
        su2Coefficients[
            relator[g,n,
                Table[
                    If[3*(k-1)+1<=i&&i<=3*k,
                        e[Mod[i-1,3]+1],
                    {{0,0},{0,0}}],{k,1,2g+n}
                ],
            rep]
        ][[j]],
        {j,1,3},{i,1,3(2g+n)}];
    (* We now have a list of all the maps that vanish on the relator. For n = 0, these are
       exactly the cocycles, but for n > 0, maybe we got too much here. *)
    cocycleSatisfied = NullSpace[r];
    If[n == 0, Return[Transpose[cocycleSatisfied]]];
    (* For n > 0, let's create once more the list of all parabolic maps and intersect with those
       that are also cocycles *)
       
    parabolicMaps=
        Flatten[Table[
            su2Coefficients[
                If[3*(k-1)+1<=i&&i<=3*k,
                    If[k<=2g,e[Mod[j-1,3]+1], e[Mod[j-1,3]+1]-matrixAdjoint[rep[[k]],e[Mod[j-1,3]+1]]],
                {{0,0},{0,0}}]
            ][[Mod[i-1,3]+1]]
           ,{k,1,2g+n},{j,1,3},{i,1,3(2g+n)}],1];
    (* The desired space is now the overlap between the above two spaces. *)
    intersection = intersectionSubspaces[cocycleSatisfied,parabolicMaps];
    Return[If[intersection=={},{},Transpose[intersection]]];
])


findB1::notarep="The matrices given do not give a representation of pi_1";
findB1[g_Integer?NonNegative,n_Integer?NonNegative,rep_List] :=(Module[{span},
    If[!isRep[g,n,rep],Message[findB1::notarep];Return[$Failed]];
    span=Table[
        su2Coefficients[
            e[Mod[j-1,3]+1]-matrixAdjoint[rep[[Floor[(i-1)/3]+1]],e[Mod[j-1,3]+1]]
        ][[Mod[i-1,3]+1]]
        ,{i,1,3*(2g+n)},{j,1,3}];
    Return[span];
])

(* Find the dimension of parabolic cohomology at a point. *)
findDimH1::notarep="The matrices given do not give a representation of pi_1";
findDimH1[g_Integer?NonNegative,n_Integer?NonNegative,rep_List]:=( Module[{Z1,B1,dimZ1,dimB1},
    If[!isRep[g,n,rep],Message[findDimH1::notarep];Return[$Failed]];
    Z1=findZ1[g,n,rep];
    B1=findB1[g,n,rep];
    dimZ1=If[Z1=={},0,MatrixRank[Z1]];
    dimB1=If[B1=={},0,MatrixRank[B1]];
    Return[dimZ1-dimB1];
])

(*
    A few words on notation: Letting a_1, b_1, ..., a_g, b_g denote the standard generators
    of pi_1 of a closed surface respectively, an action on pi_1 is given as a list whose i'th
    element is the word in the generators corresponding to the image of the i'th element in the
    above list.

    For example, the action on pi_1(torus) mapping a_1 to b_1 and b_1 to a_1^{-1} would be given
    by {{2},{-1}}. An example for a genus two surface would be
    	{{4,3,2,1,1,2,1,2,1},{2,1},{2,1,4,3,3,4,3,4,3},{4,3}}
    which is induced by a pseudo-Anosov and for instance maps b_2 to b_2 a_2.

    This is kind of easy to mess up so let's include sanity checks in everything that follows.
*)
mapWellDefined::maplength="The map should be a list of 2g+n lists";
mapWellDefined::notlistoflists="The map should be a list of lists";
mapWellDefined::badgenerators="Map contains generators not in {1, ..., 2g+n} and their inverses.";
mapWellDefined[g_Integer?NonNegative,n_Integer?NonNegative,map_List]:=( 
    If[Length[map]!=2g+n,Message[mapWellDefined::maplength];Return[False]];
    If[MemberQ[Map[ListQ,map],False],Message[mapWellDefined::notlistoflists];Return[False]];
    If[MemberQ[Flatten[Map[IntegerQ[#]&&Abs[#]>0&&Abs[#]<=2g+n&,map,{2}]],False],
        Message[mapWellDefined::badgenerators];Return[False]];
    Return[True]
)

(* Gives the identity map acting on pi_1 *)
identityMap[g_Integer?NonNegative,n_Integer?NonNegative] :=( 
    Return[Table[{i},{i,1,2g+n}]];
)

(* From a map, remove all occurences of -1,1, -2,2 etc. *)
cleanUpMap[g_Integer?NonNegative,n_Integer?NonNegative,map_List]:=( 
    (*ReplaceRepeated[map,{l1___,x_,y_,l2___}/;x==-y->{l1,l2}]*)
    ReplaceRepeated[map, {{l1___, x_, y_, l2___} /; x == -y -> {l1, l2},
                          Flatten[{l1___, Table[i, {i, 1, n}], l2___}]/;g==0 -> {l1, l2},
                          Flatten[{l1___, Table[-n-1+i, {i, 1, n}], l2___}]/;g==0 -> {l1, l2},
                          Flatten[{l1___, Table[i, {i, 1, n-1}], l2___}]/;g==0 -> {l1,-n, l2},
                          Flatten[{l1___, Table[-n+i, {i, 1, n-1}], l2___}]/;g==0 -> {l1,n, l2}
                          }]
)

(*
	From a word in the Dehn twist generators of a closed surface of genus 1 or 2,
	create the associated action on pi_1.
	The word is given as a list of integers whose absolute value does not exceed 2 (for g = 1)
	or 5 (for g = 2), and which correspond to the 2 resp. 5 Dehn twist generators. Negative
	signs denote inverses. Thus, for instance, the Anosov cat map is given by {1,-2}.
*)
twistsToMap::notintegers="The Dehn twist word should be a word of integers";
twistsToMap::illdefinedtwist="The Dehn twist list contains a non-existing twist";
twistsToMap[g_Integer/;(g==1||g==2),n_Integer/;n==0,word_List]:=( Module[{map,twists},
    (* For the empty word, return the identity map *)
    If[Length[word]==0,Return[identityMap[g,n]];];
    (* Ensure that the Dehn twist generators belong to the appropriate sets *)
    If[MemberQ[Map[IntegerQ,word],False],Message[twistsToMap::notintegers];Return[$Failed]];
    If[MemberQ[Map[Abs[#]>=1&&Abs[#]<=If[g==1,2,5]&,word],False],Message[twistsToMap::illdefinedtwist];Return[$Failed]];
    (* We begin with the identity and word our way through the list *)
    map = identityMap[g,n];
    (* Words are always written in the "wrong" order, so let's fix that *)
    twists = Reverse[word];
    (* Since pi_1 is abelian for g=1, we don't need to worry so much about orderings and orientations *)
    If[g==1,
        Do[
            Switch[twists[[i]],
                1,map=Replace[map,{2->Sequence[1,2],-2->Sequence[-2,-1]},2];,
                -1,map=Replace[map,{2->Sequence[-1,2],-2->Sequence[-2,1]},2];,

                2,map=Replace[map,{1->Sequence[1,-2],-1->Sequence[2,-1]},2];,
                -2,map=Replace[map,{1->Sequence[1,2],-1->Sequence[-2,-1]},2];
            ];
        ,{i,1,Length[twists]}];
    ];
    (* For a picture of the case g = 2, see p. 127 of my thesis. To obtain the right relations in pi_1, we transform
	   1 -> -1, 2 -> 2, 3 -> (4,3,-4), 4 -> -4. *)
    If[g==2,
        Do[
            Switch[twists[[i]],
                1,map=Replace[map,{2->Sequence[2,-1],-2->Sequence[1,-2]},2];,
                -1,map=Replace[map,{2->Sequence[2,1],-2->Sequence[-1,-2]},2];,

                2,map=Replace[map,{1->Sequence[1,2],-1->Sequence[-2,-1]},2];,
                -2,map=Replace[map,{1->Sequence[1,-2],-1->Sequence[2,-1]},2];,

                3,map=Replace[map,{
                    2->Sequence[-1,4,3,-4,2],-2->Sequence[-2,4,-3,-4,1],
                    3->Sequence[-1,4,3,-4,3,4,-3,-4,1],-3->Sequence[-1,4,3,-4,-3,4,-3,-4,1],
                    4->Sequence[4,4,-3,-4,1],-4->Sequence[-1,4,3,-4,-4]},2];,
                    -3,map=Replace[map,{2->Sequence[4,-3,-4,1,2],-2->Sequence[-2,-1,4,3,-4],
                    3->Sequence[4,-3,-4,1,3,-1,4,3,-4],-3->Sequence[4,-3,-4,1,-3,-1,4,3,-4],
                    4->Sequence[4,-1,4,3,-4],-4->Sequence[4,-3,-4,1,-4]
                    },2];,

                4,map=Replace[map,{3->Sequence[3,4],-3->Sequence[-4,-3]},2];,
                -4,map=Replace[map,{3->Sequence[3,-4],-3->Sequence[4,-3]},2];,

                5,map=Replace[map,{4->Sequence[4,-3],-4->Sequence[3,-4]},2];,
                -5,map=Replace[map,{4->Sequence[4,3],-4->Sequence[-3,-4]},2];
            ];
        ,{i,1,Length[twists]}];
    ];
    Return[cleanUpMap[g,n,map]];
])

(* Like the above, the next one takes a braid and gives a map on pi_1 (cf. the action of B_n on F_n) *)
braidsToMap::notintegers="The braid word should be a word of integers";
braidsToMap::illdefinedbraid="The list given is illdefined. All elements should be non-zero integers between -n+1 and n-1";
braidsToMap[g_Integer/;g==0,n_Integer?NonNegative,word_List]:=( Module[{map,braids,b},
    (* For the empty word, return the identity map *)
    If[Length[word]==0,Return[identityMap[g,n]];];
    (* Ensure that the generators belong to the appropriate sets *)
    If[MemberQ[Map[IntegerQ,word],False],Message[braidsToMap::notintegers];Return[$Failed]];
    If[MemberQ[Map[Abs[#]>=1&&Abs[#]<=n-1&,word],False],Message[braidsToMap::illdefinedbraid];Return[$Failed]];
    (* The braid word is usually written in its inverse form *)
    braids = Reverse[word];
    (* We loop through the word of braids and make the appropriate replacements *)
    map = identityMap[g,n];
    Do[b=braids[[i]];
        Switch[b,
          _?Positive, 
          map = Replace[map, {b -> b + 1, b + 1 -> Sequence[-b - 1, b, b + 1], 
                             -b -> -(b + 1), -(b + 1) -> Sequence[-(b + 1), -b, b + 1]}, 2];,
          _?Negative, 
          map = Replace[map, {-b -> Sequence[-b, -b + 1, b], -b + 1 -> -b, 
                               b -> Sequence[-b, b - 1, b], b - 1 -> b}, 2];
    ];
    ,{i,1,Length[braids]}];
    Return[cleanUpMap[g,n,map]];
    
])

(* The following ensures that rho is a fixed point in moduli space of a pair (f,h), where h
   is in the group; that is, that Ad(h)rho(f(gamma)) = rho(gamma). Unfortunately, h has to be
   specified by the user. *)

checkFixedPoint::notarep="The matrices given do not form a representation of pi_1";
checkFixedPoint::mapnotwelldefined="The map is not well-defined";
checkFixedPoint::matrixnotingroup="The fifth argument should be an element of SU(2)";
checkFixedPoint[g_Integer?NonNegative,n_Integer?NonNegative,rep_List,map_List,h_:IdentityMatrix[2]]:=( 
    (* A couple of sanity checks *)
    If[!isRep[g,n,rep],Message[checkFixedPoint::notarep];Return[$Failed]];
    If[!mapWellDefined[g,n,map],Message[checkFixedPoint::mapnotwelldefined];Return[$Failed]];
    If[!isInSU2[h],Message[checkFixedPoint::matrixnotingroup];Return[$Failed]];
    (* Check that rho(gamma) = Ad(h)rho(f(gamma)) for all 2g+n generators gamma *)
    Return[!MemberQ[Table[rep[[i]]==matrixAdjoint[h,wordToProduct[map[[i]],rep]],{i,1,2g+n}],False]];
)

(* Get the action on Z1 at a fixed point. Result is given in the coordinates as specified by findZ1. *)
actionOnZ1::repnotfixed="Representation is not fixed by the map";
actionOnZ1[g_Integer?NonNegative,n_Integer?NonNegative,rep_List,map_List,h_:IdentityMatrix[2]] :=(Module[{Z1,Z1basis,u,newy,newvector},
    If[!checkFixedPoint[g,n,rep,map,h],Message[actionOnZ1::repnotfixed];Return[$Failed]];
    Z1 = findZ1[g,n,rep];
    If[Z1=={},Return[{}]];
    Z1basis = Transpose[findZ1[g,n,rep]];
    Transpose[Table[
        (* Get the values of the cocycles on each basis vector *)
            u=Table[ Z1basis[[i,k]]*e[1]+Z1basis[[i,k+1]]*e[2]+Z1basis[[i,k+2]]*e[3],{k,1,3(2g+n),3}];
            (* Evaluate the result of the action of Ad(h) composed with the map *)
            newu:=Table[matrixAdjoint[h,cocycleOnWord[g,n,u,rep,map[[(k-1)/3+1]]]],{k,1,3(2g+n),3}];
            (* Write the result in the same coordinates as before *)
            newvector:=Table[su2Coefficients[newu[[Floor[(k-1)/3+1]]]][[Mod[k-1,3]+1]],{k,1,3(2g+n)}];
            (* Get the coordinates corresponding to the basis we began with *)
            LinearSolve[Transpose[Z1basis],newvector]
        ,{i,1,Length[Z1basis]}
        ]
    ]
])

(* The following computes the 1-eigenspace of the action of a map on cohomology at a fixed point *)
fixedDirections::repnotfixed="Representation is not fixed by the map";
fixedDirections[g_Integer?NonNegative,n_Integer?NonNegative,rep_List,map_List,h_:IdentityMatrix[2]]:=(
Module[{Z1basis,B1basis,action,eigenspace,eigenspaceInBasis,intersection,eigenspaceDim,intersectionDim},
    If[!checkFixedPoint[g,n,rep,map,h],Message[fixedDirections::repnotfixed];Return[$Failed]];
    (* We need the basis elements for later (so Z1basis is actually calculated twice; for performance, this should be fixed). *)
    Z1basis = Transpose[findZ1[g,n,rep]];
    B1basis = Transpose[findB1[g,n,rep]];
    (* Let us get the matrix for the action wrt. the basis of cocycles *)
    action = actionOnZ1[g,n,rep,map,h];
    If[action=={},Return[0]];
    (* Get the fixed directions *)
    eigenspace=NullSpace[action-IdentityMatrix[Length[action]]];
    (* Let us write these directions once again in the original basis *)
    eigenspaceInBasis=Table[
        Sum[
            eigenspace[[j,k]]*Z1basis[[k]],{k,1,Length[eigenspace[[j]]]}
        ]
        ,{j,1,Length[eigenspace]}
    ];
    (* Finally, we figure out the overlap with B^1. *)
    intersection=intersectionSubspaces[B1basis,eigenspaceInBasis];
    (* We can then find the dimension of the quotient as a simple difference. *)
    eigenspaceDim=If[eigenspaceInBasis!={},MatrixRank[eigenspaceInBasis],0];
    intersectionDim=If[intersection!={},MatrixRank[intersection],0];
    Return[eigenspaceDim-intersectionDim];
])
