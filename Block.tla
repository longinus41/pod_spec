------------------------------- MODULE Block -------------------------------

LOCAL INSTANCE TLC             \* For Assert()
LOCAL INSTANCE FiniteSets      \* For Cardinality()
LOCAL INSTANCE Sequences       \* For Len()
LOCAL INSTANCE Integers        \* For 1..n


Block == [id:Nat,parent:Nat]          \*Genesis block: [id:1, parent:0]
 
\*For test
\*{[id|->1,parent|->0],[id|->2,parent|->1],[id|->3,parent|->2],[id|->4,parent|->3]} 
\*{[id|->1,parent|->0],[id|->2,parent|->1],[id|->3,parent|->2],[id|->5,parent|->3],[id|->6,parent|->5]} 
 
------------------------------------------------------------------------------------------------
(*Useful operators*)

LegalBlock(b) == /\ b \in Block
                 /\ b.id /= b.parent

Equal(b1,b2) == /\ LegalBlock(b1)
                /\ LegalBlock(b2)
                /\ b1.id = b2.id
                /\ b1.parent = b2.parent

(*Add new block to local blocks. Do nothing if there is a same block or conflicting block*)
AddBlock(b,blocks) == IF ~LegalBlock(b) THEN Assert(FALSE,"Illegal block!") 
                       (*Do nothing, if the given set has same block.*)
                      ELSE IF \E tmpBlock \in blocks : tmpBlock.id = b.id THEN Print("Conflicting block!",blocks) 
                           ELSE blocks \cup {b}

(*Add new blocks to local blocks*)
AddBlocks(bs,blocks) == IF \E b \in bs : ~LegalBlock(b) THEN Assert(FALSE,"Illegal block!") 
                        ELSE LET repeated_set == {b \in bs : \E tmpBlock \in blocks : tmpBlock.id = b.id} IN
                             blocks \cup (bs\(repeated_set))



(*Determine whether the given blocks is a path*)
IsPath(blocks) == LET path == {} \cup blocks IN
                    IF path = {} \/ \E fb \in path:~LegalBlock(fb) THEN FALSE
                    ELSE IF Cardinality(path) = 1 THEN TRUE
                         ELSE IF \E b1 \in path : \E b2 \in path\{b1} : \/ b1.parent = b2.parent
                                                                        \/ b1.id = b2.id
                                                                            THEN FALSE
                              ELSE IF \E head \in path : /\ \A other \in path\{head} : /\ other.id /= head.parent
                                                                                       /\ other.parent \in {b.id : b \in path}
                                                         /\ head.parent \notin {b.id : b \in path}
                                                                            THEN TRUE
                                   ELSE FALSE
                                                      


\*IF \E b \in blocks : \/ ~LegalBlock(b)            
  \*                                     \/ \E b1 \in blocks\{b} : \/ b.id = b1.id
    \*                                                             \/ b.parent = b1.parent
      \*                                          THEN FALSE
        \*          ELSE IF Cardinality(blocks) =1 THEN TRUE          \* single block is a path
          \*             ELSE-IF 
            \*           ELSE LET id_set == {b2.id : b2 \in blocks} IN

\*IF /\ Cardinality(blocks)=1               
\*                     /\ \A b \in blocks : LegalBlock(b)
\*                             THEN TRUE
\*                  ELSE /\ \A b1 \in blocks: /\ LegalBlock(b1)
\*                                   (*No same blocks or forks*)
\*                                            /\ \A b2 \in (blocks\{b1}) : /\ b2.parent /= b1.parent
\*                                                                         /\ b2.id /= b1.id
\*                      (*all blocks except head block should have a parent which is in the blocks*)                                                 
\*                       /\ LET id_set == {ab.id: ab \in blocks} 
\*                          IN LET head == CHOOSE h \in blocks : h.parent \notin id_set 
\*                             IN \A nb \in blocks\{head} : nb.parent \in id_set


(*Determine whether there is path which starts from s to t*)
HasPath(s,t,blocks) == \E path \in SUBSET blocks : /\ s \in path
                                                   /\ t \in path
                                                   /\ IsPath(path)

(*Return the head of a given path or chain*)
HeadBlock(blocks) == IF blocks = {} THEN Assert(FALSE,"Set is null") 
                     ELSE IF Cardinality(blocks) = 1 THEN CHOOSE b \in blocks : TRUE
                          ELSE IF IsPath(blocks) THEN CHOOSE b \in blocks: /\ IsPath(blocks\{b})
                                                                           /\ \A bp \in blocks:b.parent /= bp.id
                               ELSE Assert(FALSE,"Set is not a path") 

(*Return the tail of a given path or chain*)                                          
TailBlock(blocks) == IF blocks = {} THEN Assert(FALSE,"Set is null") 
                     ELSE IF Cardinality(blocks) = 1 THEN CHOOSE b \in blocks : TRUE
                          ELSE CHOOSE b \in blocks: /\ IsPath(blocks\{b})
                                                    /\ IsPath(blocks)
                                                    /\ \E bp \in blocks:b.parent = bp.id                             
                                   
IsPrefix(path1,path2) == /\ IsPath(path1)
                         /\ IsPath(path2)
                         /\ path1 \subseteq path2
                         /\ HeadBlock(path1) = HeadBlock(path2)
                         
IsPrefixForAll(path,paths) == \A tmpPath \in paths: IsPrefix(path,tmpPath)


LongestPath(paths) == CHOOSE longest \in paths : \A tmpPath \in paths : /\ Cardinality(longest)>=Cardinality(tmpPath)
                                                                        \*/\ IsPath(tmpPath)            


(*Return the longest common prefix of given paths*)
GetPrefix(paths) == IF \E p1,p2 \in paths: Cardinality(p1 \intersect p2) = 0 /\ HeadBlock(p1)/=HeadBlock(p2) THEN Print("No prefix!",{})
                            ELSE LET prefix == {intersection \in (UNION paths):  \A path \in paths : intersection \in path}
                                  IN IF IsPath(prefix) THEN prefix
                                      ELSE Print("No prefix!",{})


GetPath(s,t,blocks) == IF ~HasPath(s,t,blocks) THEN Print("No path!",<<s,t,blocks>>)
                            ELSE LET all == SUBSET blocks IN
                                CHOOSE path \in all : /\ IsPath(path)
                                                      /\ s \in path
                                                      /\ t \in path
                                                      /\ HeadBlock(path) = s
                                                      /\ TailBlock(path) = t


(*Determine whether the given block s is ancestor of t *)                                                      
IsPrev(s,t,blocks) == LET path_set == { sub_blocks_set \in (SUBSET blocks)\{{}} : IsPath(sub_blocks_set)} IN 
                            \E path \in path_set : /\ HeadBlock(path) = s
                                                   /\ TailBlock(path) = t
                                                   /\ s/=t

                                                                                       

IsChain(blocks) == \A b \in blocks: /\ LegalBlock(b)
                                    (*Each block in chain must have a path to the head block*)
                                    /\ LET head == HeadBlock(blocks) IN HasPath(head,b,blocks)
=============================================================================
\* Modification History
\* Last modified Mon Jun 17 13:48:21 CST 2019 by tangzaiyang
\* Created Thu Jun 06 11:21:13 CST 2019 by tangzaiyang
