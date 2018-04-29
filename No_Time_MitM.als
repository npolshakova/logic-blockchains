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
}

--At the end of the attack, B falsely believes that A is communicating with him,
--and that NA and NB are known only to A and B.
pred MitM(msg1 : Message, attacker, victim, normalUser : User) {	
		
		--A sends NA to Eve, who decrypts the message with private key of Eve
		requestFromServer[msg1, attacker, normalUser]

		let msg2 = msg1.next {
		-- S responds with Eve's public key and identity, signed with server's private key
		-- A verifying S's message with public key and takes Eve's public key and stores it 
		responseFromServer[msg2, attacker, normalUser]

		let msg3 = msg2.next {
		-- A sends Eve a random N initiating contact
		initiateContact[msg3, normalUser, attacker]

		let msg4 = msg3.next {
		--Eve now knows A wants to communicate, so Eve requests A's public keys.
		requestFromServer[msg4, normalUser, attacker]

		let msg5 = msg4.next {
		-- S responds with A's public key and identity, signed with server's private key
		-- Eve verifying S's message with public key and Takes A's public key and stores it 
		responseFromServer[msg5, normalUser, attacker]

		let msg6 = msg5.next {
		-- Eve send S request for B key
		requestFromServer[msg6, victim, attacker]

		let msg7 = msg6.next {
		-- S responds with B's public key and identity, signed with server's private key
		-- Eve verifying S's message with public key and Takes B's public key and stores it 
		responseFromServer[msg7, victim, attacker]

		let msg8 = msg7.next {
		--Eve relays the message to B, pretending that A is communicating:
		msg8.sender = normalUser and msg8.reciever = victim and msg8.payload = msg3.payload
									and msg8.encrypted =attacker.contactList[victim].msg8

		let msg9 = msg8.next {	
		--B now knows A wants to communicate, so B requests A's public keys.
		requestFromServer[msg9, normalUser, victim]

		let msg10 = msg9.next {
		-- S responds with A's public key and identity, signed with server's private key
		-- B verifying S's message with public key and Takes A's public key and stores it 
		responseFromServer[msg10, normalUser, victim]

		let msg11 = msg10.next {
		--B sends NB
		 some p : ProofNonce | p.decodedNonce = msg8.payload
									and p.newNonce = victim.nonce
									and msg11.sender = victim and msg11.reciever = attacker 
									and msg11.payload =  p and msg11.encrypted = victim.contactList.msg11[normalUser] 

		let msg12 = msg11.next {
		--Eve relays NB to A
		msg12.payload = msg11.payload
 		and msg12.sender = attacker 
		and msg12.reciever = normalUser
		and msg12.encrypted = attacker.contactList.msg11[normalUser] 

		--A decrypts NB and confirms it to Eve, who learns it
		let msg13 = msg12.next {
			canDecode[normalUser, msg12] 
			and msg12.payload.decodedNonce = normalUser.nonce
			and msg13.sender = normalUser and msg13.reciever = attacker 
			and msg13.payload = msg12.payload.newNonce 
			and msg13.encrypted = normalUser.contactList.msg13[attacker]

		let msg14 = msg13.next {
		--Eve re-encrypts NB, and sends it to Bob
			msg14.sender = attacker and msg14.reciever = victim
			and msg14.payload = msg13.payload

		-- Eve  convinces B that she's decrypted it
		msg14.payload = victim.nonce
		
	}}}}}}}}}}}}}
}

--- TRACE ---

fact Traces {
	-- INITIAL STATE
	first.init 
	MitM[first, Eve, Bob, Alice]
	--ExchangeKey[first, Alice, Bob]
	all m : Message | some disj u1, u2 : User |
		SendMessage[u1, u2, m]
}

--- RUN ---

run {} for 20 Message, 20 SendableValue,  4 Request
