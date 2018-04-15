-- Time stuff = fix for MitM attack
open util/ordering[Time] -- time dependent

sig Time {}

-- all users have one public key and one private key
sig User {
	privateKey : one Key,
	publicKey : one Key
}
-- Only one Alice/Bob user
one sig Alice extends User {}
one sig Bob extends User {}

-- Should an attacker be a user?
sig Attacker {}
one sig Eve extends Attacker {}

sig SendableValue {}
sig Key extends SendableValue {}

pred init(t:Time) {
		-- All user public/private keys are unique
		all disj u1, u2 : User | u1.privateKey != u2.privateKey and u1.publicKey != u2.publicKey

		-- A user's public and private keys are not the same
		all u: User | u.publicKey != u.privateKey 
}

sig Message {
	sender : one User,
 	reciever :  one User,
	payload : one SendableValue,
	encrypted: one Key -- each message is encrypted with a public key
}

run {}
