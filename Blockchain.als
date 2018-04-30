open util/ordering[Time] -- time dependent

sig Time {
	blocks: some Block
}

sig Block {
	parent: lone Block,
	children: set Block,
	payload: set Transaction,
	hash: one Hash,
	timestamp: one Time,
	miner: one Miner
}

sig Hash {
	hashprev: one Hash,
	payload: seq Transaction
	//signature: one Key
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

//sig Key {}

abstract sig Person {
	//publicKey: one Key,
	//privateKey: one Key
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
	
	-- only the initial block is in the blockchain
	t.blocks = Blockchain.initial

	-- initial block has no parent but has children
	no Blockchain.initial.parent
	some Blockchain.initial.children
}

fact Trace {
	first.init

	-- every subsequent time unit adds one block to the blockchain
	all t: Time, t': t.next | some b: Block | b not in t.blocks and t'.blocks = t.blocks + b
																and b in t.blocks.children

	-- ensures that block timestamps correspond to their respective time
	all b: Block, t: Time, t': t.next | b.timestamp = t' iff (b in t'.blocks and b not in t.blocks)

	-- ensures that transactions have the same timestamp as the block they're in
	all b: Block, tx: Transaction | some b.payload 
												and tx in b.payload implies tx.timestamp = b.timestamp
	
	-- ensures that blocks later in the blockchain have later timestamps
	all disj b1, b2: Block | b2 in b1.children implies larger[b1.timestamp, b2.timestamp] = b2.timestamp

}

fact BlockProperties {
	-- except the initial block, all blocks have one parent and is in the blockchain
	all b: Block - Blockchain.initial | one b.parent and b in Blockchain.initial.^children

	-- a parent of a block can't be that block's child, and vice versa
	all b: Block | some b.parent implies b.parent not in b.children
						and some b.children implies b.children not in b.parent
	
	-- reflexive property of the parent-child relationship
	all disj b1, b2: Block | (b1 in b2.parent implies b2 in b1.children)
										and (b1 in b2.children implies b2 in b1.parent)

	-- no cycles and no self-loops
	no iden & children.^children
	no iden & parent.^parent

	-- all blocks are in the blockchain
	all b: Block | b in Blockchain.blocks
}

fact ForkProperties {
	-- defines fork head and chain
	all b: Block | some f: Fork | #{b.parent.children} > 1 iff (f.head = b.parent and f.chain = b.^children + b)

	-- forks occur when there it splits into at least two block
	no f: Fork | #{ f.head.children } < 2

	-- each block splits into no more than two forks (due to extremely low probability of more than two in practice)
	all b: Block | b in Fork.head implies (#{ head.b } < 3 and #{ head.b } > 0)

	-- if there is a fork that's greater than 4 blocks, the alternate fork is abandoned
	all t: Time, t': t.next | all disj f1, f2: Fork | some b: Block | (b in t'.blocks and b not in t.blocks and b in f1.chain 
																							and #{ f1.chain } > 4 and f1.head = f2.head and #{f2.chain} < 4 )
																							implies { no b2: Block | (b2 in t'.^next.blocks and b2 not in t.blocks) implies b2 in f2.chain } 
}

fact HashProperties {
	-- all hashes exist in some block
	all h: Hash | some b: Block | b.hash = h

	no iden & hashprev.^hashprev
	
	-- links previous hashes with previous blocks
--	all h: Hash, b: Block | h in b.hash implies h.prev in b.parent.hash
}

fact MinerProperties {
	-- ensures that the number of blocks created by a miner is the same as the miner's power rating
	all m: Miner | m.power > 0 and #{miner.m} = m.power
}

run {}  for 12 Block, 12 Time, 10 Fork, 4 Miner, 1 User, 1 Value, 12 Hash, 6 Transaction, 6 Int
