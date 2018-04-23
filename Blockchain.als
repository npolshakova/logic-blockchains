open util/ordering[Time] -- time dependent

sig Time {
	transactions: set Transaction
}

sig Block {
	parent: lone Block,
	child: set Block,
	payload: seq Transaction,
	hash: one Hash,
	capacity: Int
}

sig Hash {
	prev: one Hash,
	payload: seq Transaction,
	signature: one Key
}

-- subchain of the entire blockchain
sig Fork {
	chain: set Block,
	head: one Block
}

one sig Blockchain {
	blocks: set Block,
	initial: one Block
}

sig Key {}

abstract sig Person {
	publicKey: one Key,
	privateKey: one Key
}

sig Miner extends Person {
}

--sig Sig {}

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
	-- initial is the only block in the blockchain
	--Blockchain.blocks in Blockchain.initial

	no Blockchain.initial.parent
	some Blockchain.initial.child
}

fact Trace {
	first.init

	-- 
	all t: Time, tx: Transaction | some t.transactions 
												and tx in t.transactions implies tx.timestamp = t
}

fact BlockProperties {
	all b: Block - Blockchain.initial | one b.parent and b in Blockchain.initial.^child

	all b: Block | some b.parent implies b.parent not in b.child 
						and some b.child implies b.child not in b.parent	-- parent cannot be a child of the same block
	
--	all b: Block | b not in b.child and b not in b.parent -- no self-child and no self-parent
	
	all disj b1, b2: Block | (b1 in b2.parent implies b2 in b1.child)
										and (b1 in b2.child implies b2 in b1.parent)

	no iden & child.^child
	no iden & parent.^parent

	all b: Block | b in Blockchain.blocks
}

run {}  for 6 Block, 2 Time, 1 Hash, 1 Fork, 1 Key, 1 Person, 1 Value, 1 Transaction
