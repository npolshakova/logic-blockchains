-- Reach goal for the Blockchain section
-- Based on Tendermint consensus protocol: https://tendermint.com/static/docs/tendermint.pdf
 
open util/ordering[Time] -- time dependent

sig Time {
	blocks: some Block
}

sig Block {
	parent: lone Block,
	child: set Block,
	payload: set Transaction,
	timestamp: one Time,
	validator: one Validator, -- who ever proposed the block
	votes: set Validator
}



one sig Blockchain {
	blocks: set Block,
	initial: one Block
}

abstract sig Person {}

-- A Validator proposes a block to add and votes on the proposed block
-- Each validator has one vote
sig Validator extends Person {
	proposedBlock: Block,
	voteYes: Int
}


fact ValidatorProperties { 
	-- a validator proposes one or no blocks
	-- a validator votes yes 0 or more times
	-- each validator proposes two blocks
	all v : Validator | (no v.proposedBlock or one v.proposedBlock) 
								and v.voteYes > 0 or v.voteYes = 0 -- number of times validator votes "Yes"
								and #{validator.v} = 2 -- everyone proposes two block
								and #{votes.v} = v.voteYes	-- number of users that votes yes

	-- A validator always votes for their proposed block
	all b : Block | some v : Validator | b.validator = v and v in b.votes
}

sig User extends Person {
	transactions: seq Transaction
}

sig Value {}

sig Transaction {
	timestamp: one Time,
	payload: one Value,
	sender: one User,	
	receiver: lone User -- doesn't necessarily need a receiver
}

pred init(t:Time) {

	t.blocks = Blockchain.initial

	no Blockchain.initial.parent
	some Blockchain.initial.child

	-- validators have not proposed any blocks
	all v : Validator | v.proposedBlock not in t.blocks
}

fact Trace {
	first.init

	-- Propose block, vote block, if 2/3s majority, add block in
	all t: Time, t': t.next | some v : Validator | 
									(#{v.proposedBlock.votes} >  3) implies -- Greater than 3/5 yes votes
									(v.proposedBlock not in t.blocks 
									and t'.blocks = t.blocks + v.proposedBlock 
									and v.proposedBlock in t.blocks.child)

	-- ensures that block timestamps correspond to their respective time
	all b: Block, t: Time, t': t.next | b.timestamp = t' iff (b in t'.blocks and b not in t.blocks)

	-- ensures that transactions have the same timestamp as the block they're in
	all b: Block, tx: Transaction | some b.payload 
												and tx in b.payload implies tx.timestamp = b.timestamp
	
	-- ensures that blocks later in the blockchain have later timestamps
	all disj b1, b2: Block | b2 in b1.child implies larger[b1.timestamp, b2.timestamp] = b2.timestamp

}

fact BlockProperties {
	all b: Block - Blockchain.initial | one b.parent and b in Blockchain.initial.^child

	all b: Block | some b.parent implies b.parent not in b.child 
						and some b.child implies b.child not in b.parent	-- parent cannot be a child of the same block
	
	all disj b1, b2: Block | (b1 in b2.parent implies b2 in b1.child)
										and (b1 in b2.child implies b2 in b1.parent)

	no iden & child.^child
	no iden & parent.^parent

	all b: Block | b in Blockchain.blocks
}



run {}  for 10 Block, 10 Time, 5 Validator, 1 User, 1 Value, 6 Transaction
