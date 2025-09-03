(smod DOLEV-YAO is
--- enc is the data constructor for encoding
 encrypt(M, K) -> enc(M, K) .

--- decrypts messages, using a ground simulation of
--- the equality constraint
--- inv is the data constructor for inversing a key
 decrypt(enc(M,k1),inv(k1)) -> M .
 decrypt(enc(M,k2),inv(k2)) -> M .

 roles -> alice .
 roles -> bob .

***(
The protocol associates to each participant a set of actions, which are
the answers he or she returns for a given question
)

 protocol(alice, X) -> p(enc(ma1, X), enc(ma2, X)) .
 protocol(alice, p(mb1, mb2)) -> inv(k1) .
 protocol(bob, enc(ma1, k1)) -> mb1 .
 protocol(bob, enc(ma2, k2)) -> mb2 .
 ---( TODO
 protocol(bob, M) ->
 	if eq(decrypt(M, inv(k1)), ma1) then mb1 .
 protocol(bob, M) ->
 	if eq(decrypt(M, inv(k2)), ma2) then mb2 . )

***(
The following function implements the intruder capabilities model of Dolev-Yao
)
 dyStep(M) -> p(M, M) .
 dyStep(p(M1,M2)) -> M1 ? M2 .
 dyStep(M) -> enc(M, M) .
 dyStep(M) -> decrypt(M, M) .

***(
Messages that can be deduced by the intruder from a starting set of messages
)
 discover(M) -> M ? discover(discStep(M) ? M) .
 discStep(M) -> protocol(roles, M) ? dyStep(M) .

***(
Given a initial knowledge (a set of messages) for the intruder, returns true if
he discovers the secret.
)
 attack(M) -> secret(discover(M)) .
---- This function defines the patterns which are considered secrets
 secret(ma1) -> true .
ends)

(narrowing depth 30 .)

*** (width-first .)

(narrowing attack(X) .)

eof

(width-first .)

(narrowing dolevYao(X) .)

(narrowing discover(X) .)

--- (width-first .)
(depth-first .)

***(
(narrowing attack(X) .)
(width-first .)
(depth-first .)
(eval [depth= 40] attack(ma1) .)
(eval [depth= 50] attack(ma1) .)
(eval [depth= 2] attack(ma1) .)

(eval dolevYao(ma1) .)
Maude> (eval protocol(roles, dolevYao(ma1)) .)

Result: mb1
Maude> (more .)
Debug(1)>

(eval [depth= 4] protocol(roles, dolevYao(ma1)) .)
Result: mb1

Maude> (more .)

No more results.



 (width-first .)

Maude> (eval [depth= 5] protocol(roles, dolevYao(ma1)) .)

Result: mb1

(eval [depth= 5] discover(ma1) .)


en prof desde luego no va:
Maude> (eval [depth= 5] discover(ma1) .)

Result: ma1

Maude> (more .)

No more results.

Maude> (eval [depth= 4] protocol(roles, dolevYao(mb1)) .)

Result: ma2

Maude> (eval [depth= 4] protocol(roles, dolevYao(ma2)) .)

Result: mb2

Maude> (eval [depth= 4] protocol(roles, dolevYao(mb2)) .)

Result: rb2

Maude> (eval [depth= 12] attack(mb2) .)

Result:(true).Exp

Maude> (eval [depth= 30] attack(ma2) .)

Result:(true).Exp

(eval [depth= 30] attack(ma1 ? mb1) .)

Maude> (eval [depth= 20] dolevYao(ma1 ? mb1) .)

...

Result: p(ma1,mb1)

(eval [depth= 25] discover(ma1) .)

...


p(ma1,mb1)


Maude> (eval [depth= 25] protocol(roles, discover(ma1)) .)

...

Result: ma2

Maude> (eval [depth= 27] secreta(discover(ma1)) .)

Result:(true).Exp

(width-first .)
secret'(ma2) -> true .
Maude>  (eval [depth= 30] secret'(protocol(roles, discover(ma1))) .)

Result:(true).Exp


)


