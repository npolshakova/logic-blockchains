sig User {}

-- Only one Alice/Bob user
one sig Alice extends User {}
one sig Bob extends User {}

sig Key {}


-- Should an attacker be a user?
sig Attacker {}

one sig Eve extends Attacker {}
