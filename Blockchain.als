open util/ordering[Time] -- time dependent

sig Time {}

sig Block {
	parent: lone Block,
	child: set Block
	payload: seq Transaction
	hash: one Hash
}

sig Hash {
	prev: one Hash,
	payload: seq Transaction,
	signature: one Key
}

-- subchain of the entire blockchain
sig Fork {
	chain: seq Block,
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

sig Sig {}

sig User extends Person {
	transactions: seq Transaction
}

sig Value {}

sig Transaction {
	timestamp: one Time,
	payload: one Value,
	sender: one User	-- doesn't necessarily need a receiver
}

pred init(t:Time) {
	-- initial genesis block
	one Blockchain.initial

	no Blockchain.blocks
}

run {}
