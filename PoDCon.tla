------------------------------- MODULE PoDCon -------------------------------
EXTENDS Integers, FiniteSets, Sequences

INSTANCE Block 
----------------------------------------------------------------------------
CONSTANTS Validator,                   \*The set of honest validators
          FakeValidator,               \*The set of malicious or crashed validators
          ByzQuorum                    \*Set of n honest validators with f fake validators, where n >= 2f+1. Each byzantine quorum has 3f+1 validators.

ByzValidator ==  Validator \cup FakeValidator

(*******************************************Constants for TLC Model:**********************************************************)
(*Validator <- {"v1","v2","v3","v4"}*)
(*FakeValidator <- {"f1"}*)
(*ByzQuorum <- {{"v1","v2","v3","f1"},{"v4","v2","v3","f1"},{"v1","v4","v3","f1"},{"v1","v2","v4","f1"},{"v1","v2","v3","v4"}}*)
(******************************************************************************************************************************)          
ASSUME BQA == /\ Validator \cap FakeValidator = {}
              /\ \A Q \in ByzQuorum : Q \subseteq ByzValidator
              /\ \A Q1,Q2 \in ByzQuorum : Q1 \cap Q2 \cap Validator /= {}
----------------------------------------------------------------------------          
CONSTANTS Blocks

Genesis == [id|->1, parent|->0]             \*Geneis block

ASSUME BA == \A b \in Blocks : b \in Block

(*******************************************Constants for TLC Model:**********************************************************)
(*Blocks <- {[id|->1,parent|->0],[id|->2,parent|->1],[id|->3,parent|->2]}*)
(*****************************************************************************************************************************) 

---------------------------------------------------------------------------- 
(*--algorithm PoDCon
    variables localBlocks = [v \in ByzValidator |-> {Genesis}],            \*Local chain 
              beaconChain = [v \in ByzValidator |-> <<Genesis>>],          \*chain that records finalized blocks
              votedPath = [v \in ByzValidator |->{}],               \*voted path in the first round
              prefixPaths = [v \in ByzValidator |->{}],             \*all posible prefix paths of a byzvalidator
              votedPrefix = [v \in ByzValidator |->{}],             \*voted prefix in the second round
              msgs = {};                                         \*all messages 
    
    define
    (*Here we need some useful operatos, and some of them are defined in Block.tla*)
        \*IsChain(blocks) 
        \*IsPath(blocks)   
        \*Prefix(chains)          
        \*GetPath(s,t,blocks)                                 
        \*LongestPath(paths)  
        
        (*Get the set of all elements in seq*)
        SeqToSet(seq) == {seq[i] : i \in 1 .. Len(seq) }
        
        (*True for did not vote the path or any path conflicting before. *)
        (*The first block of the path should be finalized which means shoule be in the beaconChain*)             
        DidNotVotePath(v,path) == LET head == HeadBlock(path) 
                                      finalized_blocks == SeqToSet(beaconChain[v])  
                                  IN 
                                      /\ \A b \in path\{head} : b \notin finalized_blocks 
                                      /\ head \in finalized_blocks                     
    end define;
    
    (*Phase of receiving new blocks*)
    macro ReceiveNewBlock() begin
        (*For test here*)
        localBlocks[self] := AddBlocks(Blocks,localBlocks[self]);
    end macro;
    
    (*Phase of voting for paht*)    
    macro VoteForPath() begin
        with s =  beaconChain[self][Len(beaconChain[self])],  \*get the last block in beacon chain as the initiative block
             t = TailBlock(localBlocks[self]) do              \*get the last block in local blocks as the terminated block                         
             if IsPrev(s,t,localBlocks[self]) then            \*IsPrev() will return false if s=t, which means the voted path will have 2 blocks at least
                with path = GetPath(s,t,localBlocks[self]) do
                    if DidNotVotePath(self,path) then
                        votedPath[self] := path;                   \*empty the set when go to final height vote pathse 
                        msgs := msgs \cup {[type |-> "path_vote", sender |-> self, val |-> path]};
                    else 
                        skip;
                    end if;
                end with;
             else 
                skip;
             end if;
        end with;        
    end macro;
    
    
     (*Phase of voting for longest common prefix, TBA*)
    macro VoteForCommonPrefix() begin
        if votedPath[self] /= {} then
        (*wait until *)
            await \E Q \in ByzQuorum : /\ \A v \in (Q \cap Validator) : votedPath[v]/={}
                                       /\ self \in Q;                       \* may not to have this     
            with quorum_set = {Q \in ByzQuorum : /\ \A v \in (Q \cap Validator): votedPath[v]/={}
                                                 /\ self \in Q} do
                with all_prefixs = {GetPrefix({votedPath[v] : v \in (q \cap Validator)}) : q \in quorum_set} do         \*get all the prefixs from voted path of honest validators
                    votedPrefix[self] := LongestPath(all_prefixs);
                    msgs := msgs \cup {[type|-> "prefix_vote", sender |-> self, val |-> votedPrefix[self]]} ;               
                end with;
            end with;
         else 
            skip;
         end if;
    end macro;
    
    
    macro PhaseFinalHeightVote() begin
        \*
    end macro;
    
    macro FakingValidator() begin
        \*
        skip;
    end macro;
    
  (*We combine these actions into separate process decalrations for validators and fake validators*)
 fair process v \in Validator
  begin vote:    
    while TRUE do
            either
                  ReceiveNewBlock();
              or
                  VoteForPath();
              or
                  VoteForCommonPrefix();
            \*or
              \*  PhaseFinalHeightVote();
            \*or
              \*  skip;
            end either;
    end while;
    \*skip;
  end process;
  
  (*Fake validators*)
  process fv \in FakeValidator
  begin fake_vote:
    while TRUE do       
        skip;           \*do nothing
    end while;
  end process;


end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES localBlocks, beaconChain, votedPath, prefixPaths, votedPrefix, msgs

(* define statement *)
SeqToSet(seq) == {seq[i] : i \in 1 .. Len(seq) }



DidNotVotePath(v,path) == LET head == HeadBlock(path)
                              finalized_blocks == SeqToSet(beaconChain[v])
                          IN
                              /\ \A b \in path\{head} : b \notin finalized_blocks
                              /\ head \in finalized_blocks


vars == << localBlocks, beaconChain, votedPath, prefixPaths, votedPrefix, 
           msgs >>

ProcSet == (Validator) \cup (FakeValidator)

Init == (* Global variables *)
        /\ localBlocks = [v \in ByzValidator |-> {Genesis}]
        /\ beaconChain = [v \in ByzValidator |-> <<Genesis>>]
        /\ votedPath = [v \in ByzValidator |->{}]
        /\ prefixPaths = [v \in ByzValidator |->{}]
        /\ votedPrefix = [v \in ByzValidator |->{}]
        /\ msgs = {}

v(self) == /\ \/ /\ localBlocks' = [localBlocks EXCEPT ![self] = AddBlocks(Blocks,localBlocks[self])]
                 /\ UNCHANGED <<votedPath, votedPrefix, msgs>>
              \/ /\ LET s == beaconChain[self][Len(beaconChain[self])] IN
                      LET t == TailBlock(localBlocks[self]) IN
                        IF IsPrev(s,t,localBlocks[self])
                           THEN /\ LET path == GetPath(s,t,localBlocks[self]) IN
                                     IF DidNotVotePath(self,path)
                                        THEN /\ votedPath' = [votedPath EXCEPT ![self] = path]
                                             /\ msgs' = (msgs \cup {[type |-> "path_vote", sender |-> self, val |-> path]})
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << votedPath, msgs >>
                           ELSE /\ TRUE
                                /\ UNCHANGED << votedPath, msgs >>
                 /\ UNCHANGED <<localBlocks, votedPrefix>>
              \/ /\ IF votedPath[self] /= {}
                       THEN /\ \E Q \in ByzQuorum : /\ \A v \in (Q \cap Validator) : votedPath[v]/={}
                                                    /\ self \in Q
                            /\ LET quorum_set == {Q \in ByzQuorum : /\ \A v \in (Q \cap Validator): votedPath[v]/={}
                                                                    /\ self \in Q} IN
                                 LET all_prefixs == {GetPrefix({votedPath[v] : v \in (q \cap Validator)}) : q \in quorum_set} IN
                                   /\ votedPrefix' = [votedPrefix EXCEPT ![self] = LongestPath(all_prefixs)]
                                   /\ msgs' = (msgs \cup {[type|-> "prefix_vote", sender |-> self, val |-> votedPrefix'[self]]})
                       ELSE /\ TRUE
                            /\ UNCHANGED << votedPrefix, msgs >>
                 /\ UNCHANGED <<localBlocks, votedPath>>
           /\ UNCHANGED << beaconChain, prefixPaths >>

fv(self) == /\ TRUE
            /\ UNCHANGED << localBlocks, beaconChain, votedPath, prefixPaths, 
                            votedPrefix, msgs >>

Next == (\E self \in Validator: v(self))
           \/ (\E self \in FakeValidator: fv(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Validator : WF_vars(v(self))

\* END TRANSLATION

---------------------------------------------------------------------------- 
(*************************Invariants*****************************)
ChainCorrectness ==  \A i \in Validator : /\ localBlocks[i] \subseteq Blocks
                                          /\ votedPath[i] \subseteq Blocks 
                                            \*/\ prefixPaths[i] \subseteq Blocks 
                                            
GenesisInvariants == \A i \in ByzValidator : /\ Genesis \in localBlocks[i]
                                             /\ Genesis = beaconChain[i][1]


(*************************Properties*****************************)
Liveness == \A i \in Validator : /\ <>(Blocks = localBlocks[i]) 
                                 /\ <>(Blocks = votedPath[i])   \*for test
                                 /\ <>(Blocks = votedPrefix[i]) \*for test
=============================================================================
\* Modification History
\* Last modified Fri Jun 14 17:41:47 CST 2019 by tangzaiyang
\* Created Wed Jun 05 14:48:17 CST 2019 by tangzaiyang
