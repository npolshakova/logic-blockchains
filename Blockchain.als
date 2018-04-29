open util/ordering[Time] -- time dependent

sig Time {
	block: some Block
}

sig Block {
	parent: lone Block,
	child: set Block,
	payload: set Transaction,
	//hash: one Hash,
	capacity: Int,
	timestamp: one Time,
	miner: one Miner
}

/*sig Hash {
	prev: one Hash,
	payload: seq Transaction,
	signature: one Key
}*/

-- subchain of the entire blockchain
sig Fork {
	chain: set Block,
	head: one Block
}

one sig Blockchain {
	blocks: set Block,
	initial: one Block
}

/*sig Key {}*/

abstract sig Person {
	/*publicKey: one Key,
	privateKey: one Key*/
}

sig Miner extends Person {
	power: Int
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
	-- initial is the only block in the blockchain
	--Blockchain.blocks in Blockchain.initial

	no Blockchain.initial.parent
	some Blockchain.initial.child
}

fact Trace {
	first.init

	all t: Time, t': t.next | some b: Block | b not in t.block and t'.block = t.block + b

	-- ensures that block timestamps correspond to their respective time
	all b: Block, t: Time, t': t.next | b.timestamp = t' iff (b in t'.block and b not in t.block)

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

fact ForkProperties {
	-- 
	all b: Block | some f: Fork | #{b.parent.child} > 1 implies (f.head = b and f.chain = b.^child)

}

fact MinerProperties {
	all m: Miner | m.power > 0 and #{miner.m} = m.power
}

run {}  for 6 Block, 6 Time, 2 Fork, 3 Miner, 1 User, 1 Value, 6 Transaction
