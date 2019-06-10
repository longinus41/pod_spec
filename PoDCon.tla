------------------------------- MODULE PoDCon -------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Blocks,                      \*Given blocks
          \*Genesis,                     \*Genesis block definition
          Validator,                   \*The set of honest validators
          FakeValidator,               \*The set of malicious or crashed validators
          ByzQuorum                    \*Set of n honest validators with f fake validators, where n >= 2f+1. Each byzantine quorum has 3f+1 validators.
          
          
Height == Nat                          \*Block height
 
          
INSTANCE Block 


---------------------------------------------------------------------------- 
(*--algorithm PoDCon
    variables localBlocks = [v \in Validator |-> {}],            \*Local chain 
              beaconChain = [v \in Validator |-> <<>>],          \*chain that records finalized blocks
              votedPath = [v \in Validator |->{}],               \*voted path in the first round
              prefixPaths = [v \in Validator |->{}],             \*all posible prefix paths of a validator
              msgs = {};                                         \*all messages 
    
    define
    (*Here we need some useful operatos, and some of them are defined in Block.tla*)
        \*IsChain(blocks) 
        \*IsPath(blocks)   
        \*Prefix(chains)          
        \*GetPath(s,t,blocks)                                 \*Get a path with a given source block and target block
        \*LongestPath(paths) 
              
        DidNotVotePath(v,path) == TRUE                        \*Did not vote the path or any path conflicting before. TBA
    
    end define;
    
    macro Init() begin
        (*For test here*)
        localBlocks[self] := localBlocks[self] \cup Blocks;
    end macro;
    
    macro ReceiveNewBlock() begin
        (*For test here*)
        localBlocks[self] := localBlocks[self] \cup Blocks;
        \*PrintT(localBlocks[self]);
    end macro;
    
    
    macro VoteForPath() begin
        with s = beaconChain[self][Len(beaconChain[self])], \*get the last block in beacon chain as the initiative block
             t = Tail(localBlocks[self]) do                 \*get the last block in local blocks as the terminated block              
            if IsPrev(s,t,localBlocks[self]) then
                with path = GetPath(s,t,localBlocks[self]) do
                    when /\IsPath(path)
                         /\DidNotVotePath(self,path);                        
                    votedPath[self] := path;
                    msgs := msgs \cup {[type |-> "path_vote", sender |-> self, val |-> path]};      
                end with;
            else
                skip;
            end if;
        end with;        
    end macro;
    
    macro VoteForCommonPrefix() begin
        with Q \in ByzQuorum do
             with receivedPaths = {votedPath[v] : v \in Q} do
                \* if IsChain(votedPath[q])??
                prefixPaths[self] := prefixPaths[self] \cup Prefix(receivedPaths);
            end with;
        end with;
        msgs := msgs \cup {[type |-> "prefix_vote", sender |-> self, val |-> GetLonestPath(prefixPaths[self])]};       
    end macro;
    
    macro PhaseFinalHeightVote() begin
        \*
    end macro;
    
    macro FakingValidator() begin
        \*
        skip;
    end macro;
    
  (*We combine these actions into separate process decalrations for validators and fake validators*)
  process v \in Validator
  begin vote:
    Init();
    \*while TRUE do
      \*      either
        \*        VoteForPath();
          \*  or
            \*    VoteForCommonPrefix();
            \*or
              \*  PhaseFinalHeightVote();
            \*or
              \*  skip;
            \*end either;
    \*end while;\
    (*For test here*)
    \*ReceiveNewBlock();
    \*VoteForPath();
    \*skip;
  end process;
  
  (*Fake validators*)
  process fv \in FakeValidator
  begin fake_vote:
    skip;
    \*ReceiveNewBlock();
    \*while TRUE do
        \*FakingValidator();
    \*end while;
  end process;


end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES localBlocks, beaconChain, votedPath, prefixPaths, msgs, pc

(* define statement *)
DidNotVotePath(v,path) == TRUE


vars == << localBlocks, beaconChain, votedPath, prefixPaths, msgs, pc >>

ProcSet == (Validator) \cup (FakeValidator)

Init == (* Global variables *)
        /\ localBlocks = [v \in Validator |-> {}]
        /\ beaconChain = [v \in Validator |-> <<>>]
        /\ votedPath = [v \in Validator |->{}]
        /\ prefixPaths = [v \in Validator |->{}]
        /\ msgs = {}
        /\ pc = [self \in ProcSet |-> CASE self \in Validator -> "vote"
                                        [] self \in FakeValidator -> "fake_vote"]

vote(self) == /\ pc[self] = "vote"
              /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \cup Blocks]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << beaconChain, votedPath, prefixPaths, msgs >>

v(self) == vote(self)

fake_vote(self) == /\ pc[self] = "fake_vote"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << localBlocks, beaconChain, votedPath, 
                                   prefixPaths, msgs >>

fv(self) == fake_vote(self)

Next == (\E self \in Validator: v(self))
           \/ (\E self \in FakeValidator: fv(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

---------------------------------------------------------------------------- 

TypeOK == /\ \A i \in Validator : /\ localBlocks[i] \subseteq (Blocks) 
                                  /\ votedPath[i] \subseteq (Blocks) 
                                  /\ prefixPaths[i] \subseteq (Blocks) 
                                  \*/\ beaconChain[i][1] = Genesis


=============================================================================
\* Modification History
\* Last modified Mon Jun 10 11:37:09 CST 2019 by tangzaiyang
\* Created Wed Jun 05 14:48:17 CST 2019 by tangzaiyang
