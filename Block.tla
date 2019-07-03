------------------------------- MODULE Block -------------------------------

LOCAL INSTANCE TLC             \* For Assert()
LOCAL INSTANCE FiniteSets      \* For Cardinality()
LOCAL INSTANCE Sequences       \* For Len()
LOCAL INSTANCE Integers        \* For 1..n

(*In this module we define the structure of blocks, then we give some useful operators.*)

Block == [id:Nat,parent:Nat,type:{"normal","finality"}]

NormalBlock == [id:Nat,parent:Nat,type:{"normal"}]    

FinalityBlock == [id:Nat,parent:Nat,type:{"finality"}]   

(*Genesis block*)
Genesis == [id |->1, parent |->0, type |-> "normal"] 

(*Finalized block without any height finality, which may be caused by time out.*)
Empty == [id : {0}, parent : Nat, type : {"finality"}]

(*Basic axiom for block*)
AXIOM BA ==  /\ NormalBlock \subseteq Block
             /\ FinalityBlock \subseteq Block
             /\ Genesis \in NormalBlock
             /\ Empty \in FinalityBlock
\*For test
\*{[id|->1,parent|->0,type|->"normal"],[id|->2,parent|->1,type|->"normal"],[id|->3,parent|->2,type|->"normal"],[id|->4,parent|->3,type|->"normal"]} 
\*{[id|->1,parent|->0,type|->"normal"],[id|->2,parent|->1,type|->"normal"],[id|->3,parent|->2,type|->"normal"],[id|->5,parent|->3,type|->"normal"],[id|->6,parent|->5,type|->"normal"]} 
 
------------------------------------------------------------------------------------------------
(*Useful operators*)

(*True for genesis block*)
IsGenesis(b) == b = Genesis

(*True for empty finality block*)
IsEmpty(b) == b \in Empty

(*Determine whether the given block is legal.*)
LegalBlock(b) == /\ b.id /= 0
                 /\ \/ /\ b \in NormalBlock
                       /\ b.id /= b.parent
                    \/ /\ b \in FinalityBlock
                       /\ TRUE   \* maybe here need some requirements    

(*Determine wheter b1 and b2 are equivalent.*)
Equal(b1,b2) == \/ /\ b1 \in NormalBlock
                   /\ b2 \in NormalBlock
                   /\ b1.id = b2.id
                (*for finality blocks, the id can be same *)   
                \/ /\ b1 \in FinalityBlock
                   /\ b2 \in FinalityBlock
                   /\ b1.id = b2.id
                   /\ b1.parent = b2.parent

(*Note that Equal(b1,b2)=TRUE is not equivalent to b1=b2, and we give the following trivial axioms*)
AXIOM NormalBlockEquivalency == \A b1,b2 \in Block : b1=b2 => Equal(b1,b2)

AXIOM FinalityBlockEquivalency == \A b1,b2 \in Block : b1=b2 <=> Equal(b1,b2)


(*Add new block to local blocks. Do nothing if there are same blocks or conflicting blocks*)
AddBlock(b,blocks) == IF ~LegalBlock(b) THEN Assert(FALSE,"Illegal block!") 
                       (*Do nothing, if the given set has same block.*)
                      ELSE IF \E tb \in blocks : Equal(b,tb) THEN Print("Conflicting block!",blocks) 
                           ELSE blocks \cup {b}

(*Add a set of blocks to local blocks*)
AddBlocks(bs,blocks) == IF \E b \in bs : ~LegalBlock(b) THEN Assert(FALSE,"Illegal block!") 
                        ELSE LET repeated_set == {b \in bs : \E tb \in blocks : Equal(b,tb)} IN
                             blocks \cup (bs\(repeated_set))


(*True for the blocks have at least one fork.*)
HasFork(blocks) == \E b1 \in blocks : \E b2 \in blocks\{b1} : b1.parent = b2.parent

(*Determine whether the given blocks is a tree, which has a root block*)                                                      
IsTree(blocks) == LET tree == {} \cup blocks IN
                    IF tree = {} \/ \E fb \in tree:~LegalBlock(fb) THEN FALSE 
                    ELSE IF Cardinality(tree) =1 THEN TRUE
                         ELSE IF \E b1 \in tree : \E b2 \in tree\{b1} : Equal(b1,b2) THEN Assert(FALSE,"Equivalent blocks") 
                              (*Each block in the tree should have a parent in the tree except the root block*)
                              ELSE IF \E root \in tree : /\ \A other \in tree\{root} : /\ other.id /= root.parent
                                                                                       /\ other.parent \in {b.id : b \in tree}
                                                         /\ root.parent \notin {b.id : b \in tree}
                                                                            THEN TRUE
                                   ELSE FALSE

(*Determine whether the given blocks is a path, which has no fork*)
IsPath(blocks) == /\ IsTree(blocks)
                  /\ ~HasFork(blocks)


(*Simple axioms of path*)
AXIOM PathProperty1 == \A blocks : /\ IsFiniteSet(blocks)
                                   /\ IsPath(blocks) 
                                        => IsTree(blocks)


(*Determine whether there is path which starts from s to t*)
HasPath(s,t,blocks) == 
    LET F[m \in blocks] == \* True if m is a child of s
        IF m=s THEN TRUE
        ELSE IF \A b \in blocks: b.id/=m.parent THEN FALSE
        ELSE LET pm==CHOOSE b \in blocks: b.id=m.parent
             IN F[pm]
    IN F[t]
                               
(*Here we give another no-recursive version.*)
\*HasPath(s,t,blocks) == \E path \in SUBSET blocks : /\ s \in path
\*                                                   /\ t \in path
\*                                                   /\ IsPath(path)


(*Return the head of a given path*)
HeadBlock(blocks) == IF Cardinality(blocks) = 1 THEN CHOOSE b \in blocks : LegalBlock(b)
                     ELSE IF IsPath(blocks) THEN CHOOSE head \in blocks: /\ IsPath(blocks\{head})
                                                                         /\ \A b \in blocks:head.parent /= b.id
                               ELSE Assert(FALSE,"Set is not a path") 

(*Return the tail of a given path*)                                          
TailBlock(blocks) == IF Cardinality(blocks) = 1 THEN CHOOSE b \in blocks : LegalBlock(b)
                     ELSE IF IsPath(blocks) THEN CHOOSE t \in blocks: \A b \in blocks: b.parent /=t.id                                                                        
                          ELSE Assert(FALSE,"Set is not a path")  

(*Return a path of given source and terminated blocks*)
GetPath(s,t,blocks) == IF ~HasPath(s,t,blocks) THEN Assert(FALSE,"No path")
                       ELSE LET F[m\in blocks] ==
                                IF m=s THEN {s}
                                ELSE LET pm==CHOOSE b \in blocks: b.id=m.parent
                                             IN F[pm] \cup {m}
                                IN F[t]
                      
(*Here we give another no-recursive version.*)
\*GetPath(s,t,blocks) == IF ~HasPath(s,t,blocks) THEN Assert(FALSE,"No path")
\*                            ELSE LET all == SUBSET blocks IN
\*                                CHOOSE path \in all : /\ IsPath(path)
\*                                                      /\ s \in path
\*                                                      /\ t \in path
\*                                                      /\ HeadBlock(path) = s
\*                                                      /\ TailBlock(path) = t



(*Return the root of a given tree*)
RootBlock(blocks) == IF Cardinality(blocks) = 1 THEN CHOOSE b \in blocks : LegalBlock(b)
                     ELSE IF IsTree(blocks) THEN CHOOSE root \in blocks: \*/\ ~IsTree(blocks\{root})
                                                                         /\ \A b \in blocks : root.parent /= b.id
                          ELSE Assert(FALSE,"Set is not a tree") 

(*Return the height of a given block*)
GetHeight(b,blocks) == IF b \notin blocks \/ ~LegalBlock(b) THEN Assert(FALSE,"Illegal block") 
                       ELSE LET path == GetPath(RootBlock(blocks),b,blocks) IN
                            Cardinality(path)

(*Return the end of a given tree*) 
EndBlock(blocks) == IF Cardinality(blocks) = 1 THEN CHOOSE b \in blocks : LegalBlock(b)
                    ELSE CHOOSE t \in blocks: /\ IsTree(blocks\{t})
                                              /\ \A t2 \in blocks: \/ ~IsTree(blocks\{t2})
                                                                   \/ /\ IsTree(blocks\{t2})
                                                                      /\ \/ GetHeight(t,blocks)>GetHeight(t2,blocks)
                                                                         \/ /\ GetHeight(t,blocks)=GetHeight(t2,blocks)
                                                                            /\ t.id<=t2.id
                                                                     (* /\ TRUE\*choose the end block with longest path from root
                                                                     /\ TRUE\*choose the end block with lowest id   *)    


(*Simple axioms of path*)
AXIOM PathProperty2 == \A blocks : /\ IsFiniteSet(blocks)
                                   /\ IsPath(blocks) 
                                        => /\ HeadBlock(blocks) = RootBlock(blocks)
                                           /\ TailBlock(blocks) = EndBlock(blocks)






(*Return the parent block of a given block*)                            
GetParent(b,blocks) == IF /\ b.parent \in {tmp.id : tmp \in blocks} 
                          /\ b \in blocks
                       THEN
                            CHOOSE pb \in blocks : pb.id = b.parent
                       ELSE Assert(FALSE,"No parent") 


(*Get the back trace from a block b with n length*)
GetBackTrace(b,n,blocks) == 
    LET F[m \in 0..n] ==
        IF m=1 THEN {b}
        ELSE LET secondblock == HeadBlock(F[m-1])
             IN
                IF \A block \in blocks: block.id /= secondblock.parent THEN Assert(FALSE,"No trace")
                ELSE
                    LET firstblock == CHOOSE block \in blocks: block.id = secondblock.parent
                    IN {firstblock} \cup F[m-1]
    IN F[n]




(*Return the longest path*)
LongestPath(paths) == CHOOSE longest \in paths : \A path \in paths : /\ Cardinality(longest)>=Cardinality(path)
                                                                        \*/\ IsPath(tmpPath)                               

(*True for path1 is the prefix of path2*)                                                            
IsPrefix(path1,path2) == /\ IsPath(path1)
                         /\ IsPath(path2)
                         /\ path1 \subseteq path2
                         /\ HeadBlock(path1) = HeadBlock(path2)             \*may not need this

(*Return the longest common prefix of given paths*)
GetPrefix(paths) == IF \E p1,p2 \in paths: /\ Cardinality(p1 \intersect p2) = 0 
                                           /\ HeadBlock(p1)/=HeadBlock(p2) 
                                     THEN Print("No intersection",{})
                    ELSE LET prefix == {intersection \in (UNION paths):  \A path \in paths : intersection \in path}
                             IN 
                         IF IsPath(prefix) THEN prefix
                         ELSE Print("No prefix",{})
       

(*Determine whether the given block s is ancestor of t *)    
IsPrev(s,t,blocks) ==
    LET F[m \in blocks] == 
        IF m=s THEN TRUE
        ELSE IF \A b \in blocks: b.id/=m.parent THEN FALSE
        ELSE LET pm==CHOOSE b \in blocks: b.id=m.parent
             IN F[pm]
    IN F[t]             
(*Here we give another no-recursive version.*)                                                  
\*IsPrev(s,t,blocks) == LET path_set == { sub_blocks_set \in (SUBSET blocks)\{{}} : IsPath(sub_blocks_set)} IN 
\*                            \E path \in path_set : /\ HeadBlock(path) = s
\*                                                   /\ TailBlock(path) = t
\*                                                   /\ s/=t

                                                                                      
=============================================================================
\* Modification History
\* Last modified Wed Jul 03 11:27:54 CST 2019 by tangzaiyang
\* Created Thu Jun 06 11:21:13 CST 2019 by tangzaiyang
