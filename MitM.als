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


pred SendMessage(pre, post: Time, s, r: User, m : Message) {	
		m.sender = s
		m.reciever = r 
		m.encrypted = r.publicKey
		r.messagesReceived.pre in r.messagesReceived.post 
		m in  r.messagesReceived.post 
}

--At the end of the attack, B falsely believes that A is communicating with him,
--and that NA and NB are known only to A and B.
pred MitM(time1, time2: Time, attacker, victim, normalUser : User) {	
		--A sends NA to Eve, who decrypts the message with private key of Eve
		requestFromServer[time1, time2, attacker, normalUser]

		let time3 = time2.next {
		-- S responds with Eve's public key and identity, signed with server's private key
		-- A verifying S's message with public key and takes Eve's public key and stores it 
		responseFromServer[time2, time3, attacker, normalUser]

		let time4 = time3.next {
		-- A sends Eve a random N initiating contact
		initiateContact[time4, normalUser, attacker]

		let time5 = time4.next {
		--Eve now knows A wants to communicate, so Eve requests A's public keys.
		requestFromServer[time4, time5, normalUser, attacker]

		let time6 = time5.next {
		-- S responds with A's public key and identity, signed with server's private key
		-- Eve verifying S's message with public key and Takes A's public key and stores it 
		responseFromServer[time5, time6, normalUser, attacker]

		let time7 = time6.next {
		-- Eve send S request for B key
		requestFromServer[time6, time7, victim, attacker]

		let time8 = time7.next {
		-- S responds with B's public key and identity, signed with server's private key
		-- Eve verifying S's message with public key and Takes B's public key and stores it 
		responseFromServer[time7, time8, victim, attacker]

		let time9 = time8.next {
		--Eve relays the message to B, pretending that A is communicating:
		-- TODO: Alice.nonce decoded
		some m : Message | m.sender = normalUser and m.reciever = victim and m.payload = normalUser.nonce
									and m.encrypted =attacker.contactList[victim].(time9)

		let time10 = time9.next {	
		--B now knows A wants to communicate, so B requests A's public keys.
		requestFromServer[time9, time10, normalUser, victim]

		let time11 = time10.next {
		-- S responds with A's public key and identity, signed with server's private key
		-- B verifying S's message with public key and Takes A's public key and stores it 
		responseFromServer[time10, time11, normalUser, victim]

		let time12 = time11.next {
		--B sends NB
		some m : Message | some p : ProofNonce | p.decodedNonce = victim.messagesReceived.time10.payload 
									and p.newNonce = victim.nonce
									and m.sender = victim and m.reciever = attacker 
									and m.payload =  p and m.encrypted = attacker.publicKey
								    and attacker.messagesReceived.(time11) in Eve.messagesReceived.(time12) 
									and m in  Eve.messagesReceived.(time12) 

		let time13 = time12.next {
		--Eve relays NB to A
		some m : Message | some mBob : Eve.messagesReceived.(time12) | 
										m.payload = mBob.payload
										and m.sender = Eve and m.reciever = Alice and m.encrypted = Alice.publicKey

		--A decrypts NB and confirms it to Eve, who learns it
		some m : Message| some mAlice : Alice.messagesReceived.(time12) | 
																		canDecode[Alice, mAlice] 
																		and mAlice.payload.decodedNonce = Bob.nonce
																		and m.sender = Alice and m.reciever = Eve 
																		and m.payload = mAlice.payload.decodedNonce 
																		and m.encrypted = Eve.publicKey
								    									and Eve.messagesReceived.(time12) in Eve.messagesReceived.(time13) 
																		and m in  Eve.messagesReceived.(time13) 
		

		let time14 = time13.next {
		--Eve re-encrypts NB, and convinces B that she's decrypted it
		some m : Eve.messagesReceived.(time14) | 
																		m.sender = Eve and m.reciever = Bob
																		and m.payload = Bob.nonce
		
		}}}}}}}}}}}}
}

--- TRACE ---

fact Traces {
	-- INITIAL STATE
	first.init 
	--ExchangeKey[first, first.next, Alice, Bob]
	MitM[first, first.next, Eve, Bob, Alice]
	let t = first.next.next.next.next.next.next.next.next | let t' = t.next | 
		some disj u1, u2 : User | some m : Message |
		SendMessage[t, t', u1, u2, m]
}

--- RUN ---

run {} for 18 Time, 24 Message, 24 SendableValue,  4 Request
