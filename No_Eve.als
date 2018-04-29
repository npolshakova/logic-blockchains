-- Time stuff = fix for MitM attack
open util/ordering[Time] -- time dependent

sig Time {}

-- SENDABLE VALUES (KEYS) ---

abstract sig SendableValue {}
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

pred ExchangeKey(pre, post: Time) {

	-- A send S request for B key
	requestFromServer[pre, post, Bob, Alice]

	-- S responds with B's public key and identity, signed with server's private key
	-- A verifying S's message with public key and Takes B's public key and stores it 
	responseFromServer[post, post.next, Bob, Alice]

	-- A sends B a random N initiating contact
	initiateContact[post.next.next, Alice, Bob]

	--B now knows A wants to communicate, so B requests A's public keys.
	requestFromServer[post.next.next, post.next.next.next, Alice, Bob]

	-- S responds with A's public key and identity, signed with server's private key
	-- B verifying S's message with public key and Takes A's public key and stores it 
	responseFromServer[post.next.next.next, post.next.next.next.next, Alice, Bob]

	--B chooses a random Nonce, and sends it to A along with A's Nonce to prove ability to decrypt with secret key B.
	some m : Message | some p : ProofNonce | p.decodedNonce = Bob.messagesReceived.post.payload 
									and p.newNonce = Bob.nonce
									and m.sender = Bob and m.reciever = Alice 
									and m.payload =  p and m.encrypted = Alice.publicKey
								    and Alice.messagesReceived.(pre.next.next.next.next.next) in Alice.messagesReceived.(post.next.next.next.next.next) 
									and m in  Alice.messagesReceived.(post.next.next.next.next.next) 
								
	-- Alice confirms Bob got the Nonce
	some m :  Alice.messagesReceived.post |  canDecode[Alice, m] 
																		and m.payload.decodedNonce = Alice.nonce

	-- Alice sends Bob the decoded Nonce
	some m : Message | m.payload = Alice.messagesReceived.post.payload.newNonce
									and m.sender = Alice and m.reciever = Bob 
									and m.encrypted = Bob.publicKey
									and Bob.messagesReceived.(pre.next.next.next.next.next.next) in Bob.messagesReceived.(post.next.next.next.next.next.next) 
									and m in  Bob.messagesReceived.(post.next.next.next.next.next.next) 
								

	--A confirms NB to B, to prove ability to decrypt with KSA
	some m :  Bob.messagesReceived.post | canDecode[Bob, m]
																	 and m.payload = Bob.nonce 


}

pred SendMessage(pre, post: Time, s, r: User, m : Message) {	
		m.sender = s
		m.reciever = r 
		m.encrypted = r.publicKey
		r.messagesReceived.pre in r.messagesReceived.post 
		m in  r.messagesReceived.post 
}

--- TRACE ---

fact Traces {
	-- INITIAL STATE
	first.init 
	--ExchangeKey[first, first.next]
	all t : Time - last | let t' = t.next | 
		some disj u1, u2 : User | some m : Message |
		SendMessage[t, t', u1, u2, m]
}

--- RUN ---

run {} for 8 Time, 10 Message, 10 SendableValue, 2 Request
