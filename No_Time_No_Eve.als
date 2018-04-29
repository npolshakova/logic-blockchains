-- Time stuff = fix for MitM attack
open util/ordering[Message] -- message dependent

-- SENDABLE VALUES (KEYS) ---

abstract sig SendableValue {}
abstract sig Key extends SendableValue {}

-- random N
abstract sig Nonce extends SendableValue {}

-- nonces are random
fact {
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
	contactList: set ((User -> Key) -> one Message),
	privateKey : one Key,
	publicKey :  one Key,
	nonce : one Nonce
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
pred init(m:Message) {

		-- All user public/private keys are unique
		all disj u1, u2 : User | u1.privateKey != u2.privateKey and u1.publicKey != u2.publicKey 
											and u1.publicKey != u2.privateKey and u2.publicKey != u1.privateKey

		-- A user's public and private keys are not the same
		all u: User | u.publicKey != u.privateKey

		-- Only the server is in the user's contact list
		all u: User - Server | (Server -> Server.publicKey) = u.contactList.m 
										and u.publicKey = Server.contactList.m[u]

}

-- verify a user's signature
pred verify(priv, pub : Key) {
	some u : User | u.privateKey = priv and u.publicKey = pub
}

-- verify that you can decode the message **Linking between public/private key?
pred canDecode(user : User, message : Message) {
	user.publicKey = message.encrypted
}

pred requestFromServer(m: Message, requested, s: User) {
 		some r : Request |  r.requestedContact = requested and m.sender = s 
										and m.reciever = Server and m.payload =  r
										and m.encrypted = s.contactList.first[Server]
}

pred responseFromServer(m : Message, requested, s: User){
	m.sender = Server
	m.reciever = s 
	m.payload =  (Server.contactList).m[requested]
	m.encrypted = Server.privateKey 
	verify[m.encrypted, s.contactList.m[Server]] 
	s.contactList.m = s.contactList.m + (requested -> m.payload)
}

pred initiateContact(m : Message, s, r : User) {
	m.sender = s
	m.reciever = r 
	m.payload = s.nonce
	m.encrypted = s.contactList.m[r]
}

pred ExchangeKey(msg1: Message, user1, user2 : User) {

	-- A send S request for B key
	requestFromServer[msg1, user2, user1]

	let msg2 = msg1.next {
	-- S responds with B's public key and identity, signed with server's private key
	-- A verifying S's message with public key and Takes B's public key and stores it 
	responseFromServer[msg2, user2, user1]
	
	let msg3 = msg2.next {
	-- A sends B a random N initiating contact
	initiateContact[msg3, user1, user2]

	let msg4 = msg3.next {
	--B now knows A wants to communicate, so B requests A's public keys.
	requestFromServer[msg4, user1, user2]
	
	let msg5= msg4.next {
	-- S responds with A's public key and identity, signed with server's private key
	-- B verifying S's message with public key and Takes A's public key and stores it 
	responseFromServer[msg5, user1, user2]
	
	let msg6 = msg5.next { 
	--B chooses a random Nonce, and sends it to A along with A's Nonce to prove ability to decrypt with secret key B.
	some p : ProofNonce |
									p.decodedNonce = msg3.payload 
									and p.newNonce = user2.nonce
									and msg6.sender = user2 and msg6.reciever = user1 
									and msg6.payload =  p
									and msg3.reciever = user2
									and msg6.encrypted = user2.contactList.msg6[user1] 

	-- Alice confirms Bob got the Nonce
	canDecode[user1, msg6] and msg6.payload.decodedNonce = user1.nonce

	let msg7 = msg6.next {		
	-- Alice sends Bob the decoded Nonce
		msg7.payload = msg6.payload.newNonce
									and msg7.sender = user1 and msg7.reciever = user2 
									and msg7.encrypted = user2.publicKey
								
	--A confirms NB to B, to prove ability to decrypt with KSA
	canDecode[user2, msg7] and msg7.payload = user2.nonce 

	}}}}}}
}

pred SendMessage(s, r: User, m : Message) {	
		m.sender = s
		m.reciever = r 
		m.encrypted = s.privateKey or m.encrypted = r.publicKey
}

--- TRACE ---

fact Traces {
	-- INITIAL STATE
	first.init 
	ExchangeKey[first, Alice, Bob]
	-- key exchange finishes at time = 7
	all m : Message | some disj u1, u2 : User |
		SendMessage[u1, u2, m]
}

--- RUN ---

run {} for 12 Message, 12 SendableValue,  2 Request
