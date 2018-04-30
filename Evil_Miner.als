open util/ordering[Time] -- time dependent

sig Time {
	blocks: some Block
}

sig Block {
	parent: lone Block,
	children: set Block,
	payload: set Transaction,
	//hash: one Hash,
	//capacity: Int,
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

sig EvilMiner extends Miner {}

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

	all b: Block | b in Blockchain.blocks
}

fact ForkProperties {
	-- defines fork head and chain
	all b: Block | some f: Fork | #{b.parent.children} > 1 iff (f.head = b.parent and f.chain = b.^children + b)

	-- forks occur when there it splits into at least two block
	no f: Fork | #{ f.head.children } < 2

	-- each block splits into no more than two forks (due to extremely low probability of more than two in practice)
	all b: Block | b in Fork.head implies #{ head.b } < 3

	-- if there is a fork that's greater than 4 blocks, the alternate fork is abandoned
	all t: Time, t': t.next | all disj f1, f2: Fork | some b: Block | (b in t'.blocks and b not in t.blocks and b in f1.chain 
																							and #{ f1.chain } > 4 and f1.head = f2.head and #{f2.chain} < 4 )
																							implies { no b2: Block | (b2 in t'.^next.blocks and b2 not in t.blocks) implies b2 in f2.chain } 

}

fact MinerProperties {
	-- ensures that the number of blocks created by a miner is the same as the miner's power rating
	all m: Miner | m.power > 0 and #{miner.m} = m.power
}

pred EvilMinerProperties {
	-- an evil miner has 60% of the mining power in the system
	EvilMiner.power = 6

	-- there is some fork that the evil miner creates and the fork is longer than 4 blocks
	some b: Block, f: Fork | b.miner = EvilMiner and b in f.head.children and #{ f.chain } > 4

	-- if an evil miner creates a fork, then they do not mine blocks for other corresponding forks
	all disj f1, f2: Fork | EvilMiner in (f1.head.children & f1.chain).miner implies not EvilMiner in f2.chain.miner

	-- evil miner wants to split early
	Fork.head in Blockchain.initial.children
}

pred EvilMinerAttackSuccess {
	-- the fork that an evil miner creates must be longer than forks created by other users
	all disj f1, f2: Fork | EvilMiner not in (f1.head.children & f1.chain).miner and EvilMiner in (f2.head.children & f2.chain).miner 
									implies #{ f2.chain } > #{ f1.chain }
}

check {EvilMinerProperties implies EvilMinerAttackSuccess} for 10 Block, 10 Time, 2 Fork, 2 Miner, 1 User, 1 Value, 2 Transaction, 6 Int
run {EvilMinerProperties}  for 10 Block, 10 Time, 2 Fork, 2 Miner, 1 User, 1 Value, 2 Transaction, 6 Int
