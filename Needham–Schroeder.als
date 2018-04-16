-- Time stuff = fix for MitM attack
open util/ordering[Time] -- time dependent

sig Time {}

sig Entity {
	contactList: set (User -> Key)
}

-- all users have one public key and one private key
sig User extends Entity {
	privateKey : one Key,
	publicKey : one Key,
	messagesRecieved: set Message 
}
-- Only one Alice/Bob user
one sig Alice extends User {}
one sig Bob extends User {}

-- Attacker
one sig Eve extends User {}

-- Server
one sig Server extends User {}

sig SendableValue {}
sig Key extends SendableValue {}

pred init(t:Time) {
		-- All user public/private keys are unique
		all disj u1, u2 : User | u1.privateKey != u2.privateKey and u1.publicKey != u2.publicKey

		-- A user's public and private keys are not the same
		all u: User | u.publicKey != u.privateKey 

		all u: User | u in (Server.contactList).Key 
}

sig Message {
	sender : one User,
 	reciever :  one User,
	payload : one SendableValue,
	encrypted: one Key -- each message is encrypted with a public key
}

abstract sig Event {
	pre, post: Time,
	message : Message
}

sig Request extends SendableValue {
	requestedContact: one User
}

sig ExchangeKey extends Event {} {
	-- A send S request for B key
	let t' = t.next {
	some r : Request | some m : Message | r.requestedContact = Bob and m.sender = Alice 
																	and m.reciever = Server and m.payload =  r
																	and m.encrypted = Alice.privateKey
																	and Server.messagesRecieved = Server.messagesRecieved + m
	}
	
	-- S responds with B's public key and identity, signed with server's private key


	Alice.contactList.post = Alice.contactList.pre + (Bob -> Server.contactList.Bob) 
	Bob.contactList.post = Bob.contactList.pre + (Alice -> Server.contactList.Alice)
}

sig Send extends Event {} {
 
}


sig Recieve extends Event {} {

}


run {}
