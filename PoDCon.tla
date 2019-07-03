------------------------------- MODULE PoDCon -------------------------------
(*This module specifies the PoD consensus algorithm. It is an abstraction and generalization*)
(*of the PoD algorithm described in *)
(*https://github.com/freeof123/blue_paper/blob/master/en/main.pdf*)

EXTENDS Integers, FiniteSets, Sequences

(*Here we import a module which defines the structure of block and chain.*)
INSTANCE Block 
----------------------------------------------------------------------------
(*Validators are the nodes that verify the finality of blocks. We pretend that which validators*)
(*are honest and which are malicious is specified in advance.*)

(*The basic idea is that the honest validators have to execute the PoD algorithm, while the*)
(*malicious ones may try to prevent them with unpredictable actions.*)

(*Validator is the set of honest validators and FakeValidator is the set of malicious or *)
(*crashed validators.*)
(*ByzQuorum is the set of n honest validators with at most f fake validators, where n >= 2f+1.*) 
(*Each byzantine quorum has 3f+1 validators.*)
CONSTANTS Validator,                 
          FakeValidator,              
          ByzQuorum                    

(*We define ByzValidator to be the set of all real or fake validators.*)
ByzValidator ==  Validator \cup FakeValidator

(*Constants input for TLC Model:*)
(*Validator <- {"v1","v2","v3","v4"}*)
(*FakeValidator <- {"f1"}*)
(*ByzQuorum <- {{"v1","v2","v3","f1"},{"v4","v2","v3","f1"},{"v1","v4","v3","f1"},*)
(*{"v1","v2","v4","f1"},{"v1","v2","v3","v4"}}*)

(*The following are the assumptions about validators and quorums that are needed to ensure*)
(*satety of the algorithm.*)        
ASSUME BQA == /\ Validator \cap FakeValidator = {}
              /\ \A Q \in ByzQuorum : Q \subseteq ByzValidator
              /\ \A Q1,Q2 \in ByzQuorum : Q1 \cap Q2 \cap Validator /= {}
----------------------------------------------------------------------------          
(*Blocks are the set of blocks. Each block is represented as a record which contains the block id (hash)*)
(*and a pointer to the parent id (hash). For brevity, we omit the payload of block.*)

CONSTANTS Blocks

(*Constants input for TLC Model:*)
(*Blocks <- {[id|->1,parent|->0,type|->"normal"],[id|->2,parent|->1,type|->"normal"],[id|->3,parent|->2,type|->"normal"]}*)          

(*Basic assumption abouth blocks that all block id and parent id should be natural number.*)
ASSUME \A b \in Blocks : b \in NormalBlock
----------------------------------------------------------------------------
(*The length of each epoch*)
CONSTANT EpochLength

ASSUME EpochLength \in Nat
(*Constants input for TLC Model:*)
(*EpochLength <- 3*) 
---------------------------------------------------------------------------- 
(*Here we define the set Message of all possible messages.*)
(*round is the finalized round, which is represented by the last finalized block. TBA when there is no finalized one*)

PathMessage == [type : {"path_vote"}, sender : ByzQuorum, val : Blocks, round : Nat]

PrefixMessage == [type : {"prefix_vote"}, sender : ByzQuorum, val : Blocks, round : Nat]

BlockMessage == [type : {"block_vote"}, sender : ByzQuorum, val : Blocks, round : Nat]

BMessage == PathMessage \cup PrefixMessage \cup BlockMessage

(*The following lemma is the simple fact about these set of messages.*)
LEMMA BMessageLemma == \A m \in BMessage: /\ (m \in PathMessage) <=> (m.type = "path_vote")
                                          /\ (m \in PrefixMessage) <=> (m.type = "prefix_vote")

---------------------------------------------------------------------------- 
(*We now give the algorithm.*)
(*--algorithm PoDCon

    variables localBlocks = [v \in ByzValidator |-> {Genesis}],            \*Local blocks 
              finalizedChain = [v \in ByzValidator |-> <<Genesis>>],          \*chain that records finalized blocks
              votedPath = [v \in ByzValidator |->{}],               \*voted path in the first round
              \*prefixPaths = [v \in ByzValidator |->{}],             \*all posible prefix paths of a byzvalidator
              votedPrefix = [v \in ByzValidator |->{}],             \*voted prefix in the second round
              votedBlock = [v \in ByzValidator |-> Empty],          \*voted block in the final round
              msgs = {};                                         \*all messages 
    
    define
    (*Here we need some useful operators, and some of them are defined in Block.tla*)       
        (*Get the set of all elements in seq*)
        SeqToSet(seq) == {seq[i] : i \in 1 .. Len(seq) }
        
        (*True for did not vote the path or any path conflicting before. TBA*)           
        DidNotVotePath(v,path) == TRUE\*LET finalized_blocks == SeqToSet(finalizedChain[v])  
                                  \*IN  \A b \in path : b \notin finalized_blocks 
                   
    end define;
    
    (*Phase of receiving new blocks*)
    macro ReceiveNewBlock() begin
        (*For test here*)
        localBlocks[self] := AddBlocks(Blocks,localBlocks[self]);
    end macro;
    
    (*Phase of voting for paht*)    
    macro VoteForPath() begin
        with s =  finalizedChain[self][Len(finalizedChain[self])],  \*get the last block in beacon chain as the initiative block
             t = EndBlock(localBlocks[self]) do              \*get the last block in local blocks as the terminated block                         
             if IsPrev(s,t,localBlocks[self]) then            \*IsPrev() will return false if s=t, which means the voted path will have 2 blocks at least
                with path = GetPath(s,t,localBlocks[self]) do
                    if DidNotVotePath(self,path) then
                        votedPath[self] := path;                   \*empty the set when go to final height vote pathse 
                        msgs := msgs \cup {[type |-> "path_vote", sender |-> self, val |-> path, round |-> s.id]};
                    else 
                        skip;
                    end if;
                end with;
             else 
                skip;
             end if;
        end with;        
    end macro;
    
    macro VoteForPath1() begin
        with endBlock = EndBlock(localBlocks[self]) do
            if GetHeight(endBlock,localBlocks[self]) = EpochLength then         \*TBA here
                with path = GetBackTrace(endBlock,EpochLength,localBlocks[self]) do
                    if DidNotVotePath(self,path) then
                        votedPath[self] := path;
                        msgs := msgs \cup {[type |-> "path_vote", sender |-> self, val |-> path, round |-> HeadBlock(path).id]};
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
        (*wait until received paths from at least one byz quorum*)
            await \E Q \in ByzQuorum : /\ \A v \in (Q \cap Validator) : votedPath[v]/={}
                                       /\ self \in Q;                       \* no need here maybe    
            with quorum_set = {Q \in ByzQuorum : /\ \A v \in (Q \cap Validator): votedPath[v]/={}
                                                 /\ self \in Q} do
                with all_prefixs = {GetPrefix({votedPath[v] : v \in (q \cap Validator)}) : q \in quorum_set} do         \*get all the prefixs from voted path of honest validators
                    (*choose the longest prefix for honest validators*)
                    votedPrefix[self] := LongestPath(all_prefixs);
                    msgs := msgs \cup {[type|-> "prefix_vote", sender |-> self, val |-> votedPrefix[self], round |-> HeadBlock(votedPrefix[self]).id]} ;               
                end with;
            end with;
         else 
            skip;
         end if;
    end macro;
        
    macro PhaseFinalHeightVote() begin
        if votedPath[self] /={} /\ votedPrefix[self] /={} then
        (*wait until received prefixs from at least one byz quorum*)
            await \E Q \in ByzQuorum : /\ \A v \in (Q \cap Validator) : votedPrefix[v]/={}
                                       /\ self \in Q; 
            with prefix_set = {votedPrefix[v] : v \in ByzValidator } do
                 votedBlock[self]:= TailBlock(LongestPath(prefix_set)); 
                 msgs := msgs \cup {[type|-> "block_vote", sender |-> self, val |-> votedBlock[self], round |-> HeadBlock(votedPrefix[self]).id]};              
            end with
        else
            skip;
        end if;
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
                  \*VoteForPath1();
              or
                  VoteForCommonPrefix();
              or
                  PhaseFinalHeightVote();
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
VARIABLES localBlocks, finalizedChain, votedPath, votedPrefix, votedBlock, 
          msgs

(* define statement *)
SeqToSet(seq) == {seq[i] : i \in 1 .. Len(seq) }


DidNotVotePath(v,path) == TRUE


vars == << localBlocks, finalizedChain, votedPath, votedPrefix, votedBlock, 
           msgs >>

ProcSet == (Validator) \cup (FakeValidator)

Init == (* Global variables *)
        /\ localBlocks = [v \in ByzValidator |-> {Genesis}]
        /\ finalizedChain = [v \in ByzValidator |-> <<Genesis>>]
        /\ votedPath = [v \in ByzValidator |->{}]
        /\ votedPrefix = [v \in ByzValidator |->{}]
        /\ votedBlock = [v \in ByzValidator |-> Empty]
        /\ msgs = {}

v(self) == /\ \/ /\ localBlocks' = [localBlocks EXCEPT ![self] = AddBlocks(Blocks,localBlocks[self])]
                 /\ UNCHANGED <<votedPath, votedPrefix, votedBlock, msgs>>
              \/ /\ LET s == finalizedChain[self][Len(finalizedChain[self])] IN
                      LET t == EndBlock(localBlocks[self]) IN
                        IF IsPrev(s,t,localBlocks[self])
                           THEN /\ LET path == GetPath(s,t,localBlocks[self]) IN
                                     IF DidNotVotePath(self,path)
                                        THEN /\ votedPath' = [votedPath EXCEPT ![self] = path]
                                             /\ msgs' = (msgs \cup {[type |-> "path_vote", sender |-> self, val |-> path, round |-> s.id]})
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << votedPath, msgs >>
                           ELSE /\ TRUE
                                /\ UNCHANGED << votedPath, msgs >>
                 /\ UNCHANGED <<localBlocks, votedPrefix, votedBlock>>
              \/ /\ IF votedPath[self] /= {}
                       THEN /\ \E Q \in ByzQuorum : /\ \A v \in (Q \cap Validator) : votedPath[v]/={}
                                                    /\ self \in Q
                            /\ LET quorum_set == {Q \in ByzQuorum : /\ \A v \in (Q \cap Validator): votedPath[v]/={}
                                                                    /\ self \in Q} IN
                                 LET all_prefixs == {GetPrefix({votedPath[v] : v \in (q \cap Validator)}) : q \in quorum_set} IN
                                   /\ votedPrefix' = [votedPrefix EXCEPT ![self] = LongestPath(all_prefixs)]
                                   /\ msgs' = (msgs \cup {[type|-> "prefix_vote", sender |-> self, val |-> votedPrefix'[self], round |-> HeadBlock(votedPrefix'[self]).id]})
                       ELSE /\ TRUE
                            /\ UNCHANGED << votedPrefix, msgs >>
                 /\ UNCHANGED <<localBlocks, votedPath, votedBlock>>
              \/ /\ IF votedPath[self] /={} /\ votedPrefix[self] /={}
                       THEN /\ \E Q \in ByzQuorum : /\ \A v \in (Q \cap Validator) : votedPrefix[v]/={}
                                                    /\ self \in Q
                            /\ LET prefix_set == {votedPrefix[v] : v \in ByzValidator } IN
                                 /\ votedBlock' = [votedBlock EXCEPT ![self] = TailBlock(LongestPath(prefix_set))]
                                 /\ msgs' = (msgs \cup {[type|-> "block_vote", sender |-> self, val |-> votedBlock'[self], round |-> HeadBlock(votedPrefix[self]).id]})
                       ELSE /\ TRUE
                            /\ UNCHANGED << votedBlock, msgs >>
                 /\ UNCHANGED <<localBlocks, votedPath, votedPrefix>>
           /\ UNCHANGED finalizedChain

fv(self) == /\ TRUE
            /\ UNCHANGED << localBlocks, finalizedChain, votedPath, 
                            votedPrefix, votedBlock, msgs >>

Next == (\E self \in Validator: v(self))
           \/ (\E self \in FakeValidator: fv(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Validator : WF_vars(v(self))

\* END TRANSLATION

---------------------------------------------------------------------------- 
(*************************Invariants*****************************)
ChainCorrectness ==  \A i \in Validator : /\ localBlocks[i] \subseteq Block
                                          /\ votedPath[i] \subseteq Blocks 
                                            \*/\ prefixPaths[i] \subseteq Blocks 
                                            
GenesisInvariants == \A i \in ByzValidator : /\ Genesis \in localBlocks[i]
                                             /\ Genesis = finalizedChain[i][1]




(*************************Properties*****************************)
Liveness == \A i \in Validator : /\ <>(Blocks = localBlocks[i]) 
                                 /\ <>(Blocks = votedPath[i])   \*for test
                                 /\ <>(Blocks = votedPrefix[i]) \*for test
=============================================================================
\* Modification History
\* Last modified Wed Jul 03 11:58:09 CST 2019 by tangzaiyang
\* Created Wed Jun 05 14:48:17 CST 2019 by tangzaiyang
