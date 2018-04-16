-- Time stuff = fix for MitM attack
open util/ordering[Time] -- time dependent

sig Time {}

abstract sig Entity {
	contactList: set ((User -> one Key) -> Time)
}

-- all users have one public key and one private key
abstract sig User extends Entity {
	privateKey :  Key,
	publicKey :   Key,
	messagesReceived: set (Message -> Time) 
}
-- Only one Alice/Bob user
one sig Alice extends User {}
one sig Bob extends User {}

-- Attacker
one sig Eve extends User {}

-- Server
one sig Server extends User {}

abstract sig SendableValue {}
sig Key extends SendableValue {}

pred init(t:Time) {
		-- number of keys = number of user * 2
		--#{Key} = #{User} + #{User}

		-- All user public/private keys are unique
		all disj u1, u2 : User | u1.privateKey != u2.privateKey and u1.publicKey != u2.publicKey 
											and u1.publicKey != u2.privateKey and u2.publicKey != u1.privateKey
									--		and (u1 != Server implies u1.publicKey in Server.contactList.t[u1]) 
									--		and (u2 != Server implies u2.publicKey in Server.contactList.t[u2])

		-- A user's public and private keys are not the same
		all u: User | u.publicKey != u.privateKey 

		-- Only the server is in the user's contact list
		all u: User - Server | (Server -> Server.publicKey) in u.contactList.t and #{u.contactList.t} = 1
}

sig Message {
	sender : one User,
 	reciever :  one User,
	payload : one SendableValue,
	encrypted: one Key -- each message is encrypted with a public key
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
	-- A verifying S's message with public key and Takes B's public key and stores it 
	some m : Message | m.sender = Server and m.reciever = Alice and m.payload =  (Server.contactList)[Bob].pre
																	and m.encrypted = Server.privateKey 
																	and Alice.messagesReceived.post = Alice.messagesReceived.pre + m
																	and verify[m.encrypted, Alice.contactList[Server].pre] 
																	and Alice.contactList.post = Alice.contactList.pre + (Bob -> m.payload)

--	let m = Message {
		 --m.sender = Server 
		--and m.reciever = Alice and m.payload =  (Server.contactList)[Bob].pre and m.encrypted = Server.privateKey 
		--and m in Alice.messagesReceived.post and m not in Alice.messagesReceived.pre and verify[m.encrypted, Alice.contactList[Server].pre]
		--
	--}

	-- A sends B a random N initiating contact
	--some m : Message | m.sender = Alice and m.reciever = Bob and m.payload =  Nonce
		--															and m.encrypted = Server.privateKey

	--Alice.contactList = Alice.contactList + (Bob -> (Server.contactList)[Bob]) 
	--Bob.contactList = Bob.contactList + (Alice -> (Server.contactList)[Alice])
}

pred SendMessage(pre, post: Time, sender, reciever: User, message : Message) {

}

fact Traces {
	-- INITIAL STATE
	first.init 
--	ExchangeKey[first, first.next]
	all t : Time - last | let t' = t.next | 
		some disj u1, u2 : User | some m : Message |
		SendMessage[t, t', u1, u2, m]
}


run {} for 5 Time, 12 Key, 12 SendableValue, 12 Message
