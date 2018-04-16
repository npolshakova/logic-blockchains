-- Time stuff = fix for MitM attack
open util/ordering[Time] -- time dependent

sig Time {}

sig Entity {
	contactList: set ((User -> Key) -> Time)
}

-- all users have one public key and one private key
sig User extends Entity {
	privateKey : one  Key,
	publicKey :  one Key,
	messagesReceived: set (Message -> Time) 
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

		all u: User | u in Server.contactList.t.Key
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

-- random N
sig Nonce extends SendableValue {}

pred verify(priv, pub : Key) {
	some u : User | u.privateKey = priv and u.publicKey = pub
}

pred ExchangeKey(pre, post: Time) {
	-- A send S request for B key
	some r : Request | some m : Message | r.requestedContact = Bob and m.sender = Alice 
																	and m.reciever = Server and m.payload =  r
																	and m.encrypted = Alice.privateKey 
																	and Server.messagesReceived.post = Server.messagesReceived.pre + m
	
	-- S responds with B's public key and identity, signed with server's private key
	some m : Message | m.sender = Server and m.reciever = Alice and m.payload =  (Server.contactList)[Bob].pre
																	and m.encrypted = Server.privateKey 
																	and Alice.messagesReceived.post = Alice.messagesReceived.pre + m

	-- A verifying S's message with public key and Takes B's public key and stores it 
	let m = Message {
		 m.sender = Server and m.reciever = Alice and m.payload =  (Server.contactList)[Bob].pre and m.encrypted = Server.privateKey and
		 m in Alice.messagesReceived.post and m not in Alice.messagesReceived.pre and verify[m.encrypted, Alice.contactList[Server].pre]
		and Alice.contactList.post = Alice.contactList.pre + (Bob -> m.payload)
	}

	-- A sends B a random N initiating contact
	some m : Message | m.sender = Alice and m.reciever = Bob and m.payload =  Nonce
																	and m.encrypted = Server.privateKey

	Alice.contactList = Alice.contactList + (Bob -> (Server.contactList)[Bob]) 
	Bob.contactList = Bob.contactList + (Alice -> (Server.contactList)[Alice])
}

sig Send extends Event {} {
 
}


sig Recieve extends Event {} {

}

fact Traces {
	-- INITIAL STATE
	first.init 
}


run {}
