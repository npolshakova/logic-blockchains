-- Time stuff = fix for MitM attack
open util/ordering[Time] -- time dependent

sig Time {}

abstract sig Entity {
	contactList: set ((User -> Key) -> Time)
}

-- all users have one public key and one private key
abstract sig User extends Entity {
	privateKey : one Key,
	publicKey :  one Key,
	nonce : one Nonce,
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

		-- A user's public and private keys are not the same
		all u: User | u.publicKey != u.privateKey 

		-- Only the server is in the user's contact list
		all u: User - Server | (Server -> Server.publicKey) = u.contactList.t 
										and u.publicKey = Server.contactList.t[u]

}

sig Message {
	sender : one User,
 	reciever :  one User,
	payload : one SendableValue,
	encrypted: one Key -- each message is encrypted with a public key
}

fact {
	-- the sender is never the reciever and vice versa
	all m : Message | m.sender != m.reciever
	-- users never send their private keys 
	all m : Message | some u : User | m.payload != u.privateKey
}

sig Request extends SendableValue {
	requestedContact: one User
}

-- random N
sig Nonce extends SendableValue {}

-- nonces are random
fact {
	all disj n1, n2 : Nonce | n1 != n2
}

sig ProofNonce extends SendableValue {
	decodedNonce: Nonce,
	newNonce : Nonce
}

pred verify(priv, pub : Key) {
	some u : User | u.privateKey = priv and u.publicKey = pub
}

pred canDecode(user : User, message : Message) {
	user.publicKey = message.encrypted
}


pred ExchangeKey(pre, post: Time) {
	-- TODO: make generic for user1, user2. Abstract out Server request and response

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


	-- A sends B a random N initiating contact
	some m : Message | m.sender = Alice and m.reciever = Bob and m.payload = Alice.nonce
									and m.encrypted = Bob.publicKey


	--B now knows A wants to communicate, so B requests A's public keys.
	some r : Request | some m : Message | r.requestedContact = Alice and m.sender = Bob 
																	and m.reciever = Server and m.payload =  r
																	and m.encrypted = Server.publicKey 
																	and Server.messagesReceived.post = Server.messagesReceived.pre + m
	

	-- S responds with A's public key and identity, signed with server's private key
	-- B verifying S's message with public key and Takes A's public key and stores it 
		some m : Message | m.sender = Server and m.reciever = Bob and m.payload =  (Server.contactList)[Alice].pre
																	and m.encrypted = Server.privateKey 
																	and Bob.messagesReceived.post = Bob.messagesReceived.pre + m
																	and verify[m.encrypted, Bob.contactList[Server].pre] 
																	and Bob.contactList.post = Bob.contactList.pre + (Alice -> m.payload)

	--B chooses a random Nonce, and sends it to A along with A's Nonce to prove ability to decrypt with secret key B.
	some m : Message | some p : ProofNonce | p.decodedNonce = Bob.messagesReceived.post.payload 
									and p.newNonce = Bob.nonce
									and m.sender = Bob and m.reciever = Alice 
									and m.payload =  p and m.encrypted = Alice.publicKey
									and Alice.messagesReceived.post = Alice.messagesReceived.pre + m

	-- Alice confirms Bob got the Nonce
	some m :  Alice.messagesReceived.post |  canDecode[Alice, m] 
																		and m.payload.decodedNonce = Alice.nonce

	-- Alice sends Bob the decoded Nonce
	some m : Message | m.payload = Alice.messagesReceived.post.payload.newNonce
									and m.sender = Alice and m.reciever = Bob 
									and m.encrypted = Bob.publicKey
									and Bob.messagesReceived.post = Bob.messagesReceived.pre + m

	--A confirms NB to B, to prove ability to decrypt with KSA
	some m :  Bob.messagesReceived.post | canDecode[Bob, m]
																	 and m.payload.decodedNonce = Bob.nonce 

}

pred SendMessage(pre, post: Time, s, r: User, m : Message) {
		--m.sender = r
		--m.reciever = r 
		--m.encrypted = r.publicKey
		--r.messagesReceived.post = r.messagesReceived.pre + m
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
