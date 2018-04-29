-- Time stuff = fix for MitM attack
open util/ordering[Time] -- time dependent

sig Time {}

-- SENDABLE VALUES (KEYS) ---

abstract sig SendableValue {
	verifiedSender: one User
}
abstract sig Key extends SendableValue {}

-- random N
abstract sig Nonce extends SendableValue {}

-- nonces are random
fact {
	--all disj n1, n2 : Nonce | n1 != n2
	all disj u1, u2: User | u1.nonce != u2.nonce
}

-- Two values sent: original decoded nonce and new nonce
abstract sig ProofNonce extends SendableValue {
	decodedNonce: one Nonce,
	newNonce : one Nonce
}

--- USERS ---

-- all users have one public key and one private key
abstract sig User {
	contactList: set ((User -> Key) -> Time),
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

--- MESSAGE ---

abstract sig Message {
	sender : one User,
 	reciever :  one User,
	payload : one SendableValue,
	encrypted: one Key -- each message is encrypted with a public key
}

abstract sig Request extends SendableValue {
	requestedContact: one User
}

fact {
		all m : Message | m.sender != m.reciever
}

--- EVENTS ---

-- Initial State
pred init(t:Time) {

		-- All user public/private keys are unique
		all disj u1, u2 : User | u1.privateKey != u2.privateKey and u1.publicKey != u2.publicKey 
											and u1.publicKey != u2.privateKey and u2.publicKey != u1.privateKey

		-- A user's public and private keys are not the same
		all u: User | u.publicKey != u.privateKey and no u.messagesReceived.t

		-- Only the server is in the user's contact list
		all u: User - Server | (Server -> Server.publicKey) = u.contactList.t 
										and u.publicKey = Server.contactList.t[u]

}

-- verify a user's signature
pred verify(priv, pub : Key) {
	some u : User | u.privateKey = priv and u.publicKey = pub
}

-- verify that you can decode the message **Linking between public/private key?
pred canDecode(user : User, message : Message) {
	user.publicKey = message.encrypted
}

pred requestFromServer(pre,post: Time, requested, s: User) {
 		some r : Request | some m : Message | r.requestedContact = requested and m.sender = s 
																	and m.reciever = Server and m.payload =  r
																	and m.encrypted = s.privateKey 
																	and Server.messagesReceived.post = Server.messagesReceived.pre + m
}

pred responseFromServer(pre,post: Time, requested, s: User){
	some m : Message | m.sender = Server and m.reciever = s and m.payload =  (Server.contactList)[requested].pre
																	and m.encrypted = Server.privateKey 
																	and s.messagesReceived.post = s.messagesReceived.pre + m
																	and verify[m.encrypted, s.contactList[Server].pre] 
																	and s.contactList.post = s.contactList.pre + (requested -> m.payload)

}

pred initiateContact(t: Time, s, r : User) {
	some m : Message | m.sender = s and m.reciever = r and m.payload = s.nonce
									and m.encrypted = s.contactList[r].t
}

pred ExchangeKey(pre, post: Time, user1, user2 : User) {

	-- A send S request for B key
	requestFromServer[pre, post, user2, user1]

	-- S responds with B's public key and identity, signed with server's private key
	-- A verifying S's message with public key and Takes B's public key and stores it 
	responseFromServer[post, post.next, user2, user1]

	-- A sends B a random N initiating contact
	initiateContact[post.next.next, user1, user2]

	--B now knows A wants to communicate, so B requests A's public keys.
	requestFromServer[post.next.next, post.next.next.next, user1, user2]

	-- S responds with A's public key and identity, signed with server's private key
	-- B verifying S's message with public key and Takes A's public key and stores it 
	responseFromServer[post.next.next.next, post.next.next.next.next, user1, user2]

	--B chooses a random Nonce, and sends it to A along with A's Nonce to prove ability to decrypt with secret key B.
	some m : Message | some p : ProofNonce | p.decodedNonce = user2.messagesReceived.post.payload 
									and p.newNonce = user2.nonce
									and m.sender = user2 and m.reciever = user1 
									and m.payload =  p and m.encrypted = user1.publicKey
								    and user1.messagesReceived.(pre.next.next.next.next.next) in user1.messagesReceived.(post.next.next.next.next.next) 
									and m in  user1.messagesReceived.(post.next.next.next.next.next) 
								
	-- Alice confirms Bob got the Nonce
	some m :  user1.messagesReceived.post |  canDecode[user1, m] 
																		and m.payload.decodedNonce = user1.nonce

	-- Alice sends Bob the decoded Nonce
	some m : Message | m.payload = user1.messagesReceived.post.payload.newNonce
									and m.sender = user1 and m.reciever = user2 
									and m.encrypted = user2.publicKey
									and user2.messagesReceived.(pre.next.next.next.next.next.next) in user2.messagesReceived.(post.next.next.next.next.next.next) 
									and m in  user2.messagesReceived.(post.next.next.next.next.next.next) 
								

	--A confirms NB to B, to prove ability to decrypt with KSA
	some m :  user2.messagesReceived.post | canDecode[user2, m]
																	 and m.payload = user2.nonce 


}

pred SendMessage(pre, post: Time, s, r: User, m : Message) {	
		m.sender = s
		m.reciever = r 
		m.encrypted = r.publicKey
		r.messagesReceived.pre in r.messagesReceived.post 
		m in  r.messagesReceived.post 
}

--At the end of the attack, B falsely believes that A is communicating with him, and that NA and NB are known only to A and B.
pred MitM(pre, post: Time) {	
		--A sends NA to Eve, who decrypts the message with private key of Eve
		requestFromServer[pre, post, Eve, Alice]

		-- S responds with Eve's public key and identity, signed with server's private key
		-- A verifying S's message with public key and takes Eve's public key and stores it 
		responseFromServer[post, post.next, Eve, Alice]

		-- A sends Eve a random N initiating contact
		initiateContact[post.next.next, Alice, Eve]

		--Eve now knows A wants to communicate, so Eve requests A's public keys.
		requestFromServer[post.next.next, post.next.next.next, Alice, Eve]

		-- S responds with A's public key and identity, signed with server's private key
		-- Eve verifying S's message with public key and Takes A's public key and stores it 
		responseFromServer[post.next.next.next, post.next.next.next.next, Alice, Eve]

		-- Eve send S request for B key
		requestFromServer[post.next.next.next.next, post.next.next.next.next.next, Bob, Eve]

		-- S responds with B's public key and identity, signed with server's private key
		-- Eve verifying S's message with public key and Takes B's public key and stores it 
		responseFromServer[post.next.next.next.next.next, post.next.next.next.next.next.next, Bob, Eve]

		--Eve relays the message to B, pretending that A is communicating:
		-- TODO: Alice.nonce decoded
		some m : Message | m.sender = Alice and m.reciever = Bob and m.payload = Alice.nonce
									and m.encrypted = Eve.contactList[Bob].(post.next.next.next.next.next.next)

		--B now knows A wants to communicate, so B requests A's public keys.
		requestFromServer[post.next.next.next.next.next.next.next, post.next.next.next.next.next.next.next.next, Alice, Bob]

		-- S responds with A's public key and identity, signed with server's private key
		-- B verifying S's message with public key and Takes A's public key and stores it 
		responseFromServer[post.next.next.next.next.next.next.next.next, post.next.next.next.next.next.next.next.next.next, Alice, Bob]

		--B sends NB
		some m : Message | some p : ProofNonce | p.decodedNonce = Bob.messagesReceived.post.payload 
									and p.newNonce = Bob.nonce
									and m.sender = Bob and m.reciever = Eve 
									and m.payload =  p and m.encrypted = Eve.publicKey
								    and Eve.messagesReceived.(post.next.next.next.next.next.next.next.next.next) in Eve.messagesReceived.(post.next.next.next.next.next.next.next.next.next.next) 
									and m in  Eve.messagesReceived.(post.next.next.next.next.next.next.next.next.next.next) 

		--Eve relays NB to A
		some m : Message | some mBob : Eve.messagesReceived.(post.next.next.next.next.next.next.next.next.next.next.next) | 
										m.payload = mBob.payload
										and m.sender = Eve and m.reciever = Alice and m.encrypted = Alice.publicKey

		--A decrypts NB and confirms it to Eve, who learns it
		some m : Message| some mAlice : Alice.messagesReceived.(post.next.next.next.next.next.next.next.next.next.next.next) | 
																		canDecode[Alice, mAlice] 
																		and mAlice.payload.decodedNonce = Bob.nonce
																		and m.sender = Alice and m.reciever = Eve 
																		and m.payload = mAlice.payload.decodedNonce 
																		and m.encrypted = Eve.publicKey
								    									and Eve.messagesReceived.(post.next.next.next.next.next.next.next.next.next.next.next) in Eve.messagesReceived.(post.next.next.next.next.next.next.next.next.next.next.next) 
																		and m in  Eve.messagesReceived.(post.next.next.next.next.next.next.next.next.next.next.next.next) 
		

		--Eve re-encrypts NB, and convinces B that she's decrypted it
		some m : Eve.messagesReceived.(post.next.next.next.next.next.next.next.next.next.next.next.next) | 
																		m.sender = Eve and m.reciever = Bob
																		and m.payload = Bob.nonce
		
		
}

--- TRACE ---

fact Traces {
	-- INITIAL STATE
	first.init 
	MitM[first, first.next]
	all t : Time - last | let t' = t.next | 
		some disj u1, u2 : User | some m : Message |
		SendMessage[t, t', u1, u2, m]
}

--- Fact: Check sender
fact Sender {
	all m : Message | m.payload.verifiedSender = m.sender
}

--- RUN ---

run {} for 18 Time, 24 Message, 24 SendableValue,  4 Request
