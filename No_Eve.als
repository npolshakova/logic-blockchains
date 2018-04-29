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

pred ExchangeKey(time1, time2: Time, user1, user2 : User) {

	-- A send S request for B key
	requestFromServer[time1, time2, user2, user1]

	let time3 = time2.next {
	-- S responds with B's public key and identity, signed with server's private key
	-- A verifying S's message with public key and Takes B's public key and stores it 
	responseFromServer[time2, time3, user2, user1]

	let time4 = time3.next {
	-- A sends B a random N initiating contact
	initiateContact[time4, user1, user2]

	let time5 = time4.next {
	--B now knows A wants to communicate, so B requests A's public keys.
	requestFromServer[time4, time5, user1, user2]

	let time6 = time5.next {
	-- S responds with A's public key and identity, signed with server's private key
	-- B verifying S's message with public key and Takes A's public key and stores it 
	responseFromServer[time5, time6, user1, user2]

	let time7 = time6.next { 
	--B chooses a random Nonce, and sends it to A along with A's Nonce to prove ability to decrypt with secret key B.
	some m : Message | some p : ProofNonce | p.decodedNonce = user2.messagesReceived.time7.payload 
									and p.newNonce = user2.nonce
									and m.sender = user2 and m.reciever = user1 
									and m.payload =  p and m.encrypted = user1.publicKey
								    and user1.messagesReceived.(time6) in user1.messagesReceived.(time7) 
									and m in  user1.messagesReceived.(time7) 
						
	-- Alice confirms Bob got the Nonce
	some m :  user1.messagesReceived.time7 |  canDecode[user1, m] 
																		and m.payload.decodedNonce = user1.nonce

	let time8 = time7.next {		
	-- Alice sends Bob the decoded Nonce
	some m : Message | m.payload = user1.messagesReceived.time8.payload.newNonce
									and m.sender = user1 and m.reciever = user2 
									and m.encrypted = user2.publicKey
									and user2.messagesReceived.(time7) in user2.messagesReceived.(time8) 
									and m in  user2.messagesReceived.(time8) 
								

	--A confirms NB to B, to prove ability to decrypt with KSA
	some m :  user2.messagesReceived.time8 | canDecode[user2, m]
																	 and m.payload = user2.nonce 

	}}}}}}
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
	ExchangeKey[first, first.next, Alice, Bob]
	-- key exchange finishes at time = 8
	let t = first.next.next.next.next.next.next.next.next | let t' = t.next | 
		some disj u1, u2 : User | some m : Message |
		SendMessage[t, t', u1, u2, m]
}

--- RUN ---

run {} for 18 Time, 24 Message, 24 SendableValue,  4 Request
