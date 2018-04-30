__________.__                 __   .__        
\______   \  |   ____   ____ |  | _|__| ____  
 |    |  _/  |  /  _ \_/ ___\|  |/ /  |/ __ \ 
 |    |   \  |_(  <_> )  \___|    <|  \  ___/ 
 |______  /____/\____/ \___  >__|_ \__|\___  >
        \/                 \/     \/       \/ 

Modeling the Needham-Schroeder key-exchange protocol and Blockchains in alloy.

Presented by:
                     .__         .__            __         .__          ._______________   
  ____ ______   ____ |  |   _____|  |__ _____  |  | __     |  |   ____  |   ____/\   _  \  
 /    \\____ \ /  _ \|  |  /  ___/  |  \\__  \ |  |/ /     |  | _/ ___\ |____  \ /  /_\  \ 
|   |  \  |_> >  <_> )  |__\___ \|   Y  \/ __ \|    <      |  |_\  \___ /       \\  \_/   \
|___|  /   __/ \____/|____/____  >___|  (____  /__|_ \ /\  |____/\___  >______  / \_____  /
     \/|__|                    \/     \/     \/     \/ )/            \/       \/        \/ 
npolshak, lc50     


-----------------------------Needham-Schroeder Key-Exchange Files----------------------------

[Foundation goal] No_Time_No_Eve.als: The Needham-Schroeder key-exchange with no attacker, 
Eve. This illustrates a normal key change between two users, Alice an Bob. In this version
the steps are based on messages sent. The message sig has an ordering because it is assumed 
only one message is sent at a given time. 

[Target goal] No_Time_MitM.als: This shows the Man in the Middle Attacker with the
Needham-Schroeder key-exchange where Eve pretends to be Alice to Bob. In this version the
steps are based on messages sent. The message sig has an ordering because it is assumed only
one message is sent at a given time. 

[Target goal] No_Time_Fixed.als: This shows how the Man in the Middle Attacker can be
fixed by changing the message payload to include the sender's information and a fact to 
check that this is valid. Normal key exchange still works here, but the MitM attack will
result in no instances. In this version the steps are based on messages sent. The message 
sig has an ordering because it is assumed only one message is sent at a given time. 

(old) Time_No_Eve.als: The Needham-Schroeder key-exchange with no attacker, Eve. This 
illustrates a normal key change between two users, Alice an Bob. This version has a 
Time sig which is used to determine when messages are sent and recieved. 

(old) Time_MitM.als: This shows the Man in the Middle Attacker with the Needham-Schroeder
key-exchange where Eve pretends to be Alice to Bob. This version has a Time sig which is
used to determine when messages are sent and recieved. 

(old) Time_Fixed.als: This shows how the Man in the Middle Attacker can be fixed by changing 
the message payload to include the sender's information and a fact to check that this is valid.
Normal key exchange still works here, but the MitM attack will result in no instances. This 
version has a Time sig which is used to determine when messages are sent and received. 


--------------------------------------Blockchain Files--------------------------------------

[Foundation goal] Blockchain.als: This models a basic blockchain and demonstrates forking, 
block addition to a blockchain and proof of work where there are no malicious miners. Each 
miner has a random amount of computational power.

[Target goal] EvilMiner.als: This demonstrates a 51% attack where one miner has over 51% 
of the computational power in the network. This is modeled as the miner having a 
computational power level of 6 (out of 10). Once a miner has more than 50% of the
computational power, it is always possible for them to grow their preferred fork faster 
than any other alternative forks, even if their fork is malicious.

[Reach goal] BFT_Blockchain.als: This demonstrates an alternative to proof of work,
using a Byzantine fault tolerant protocol with a consensus based block addition based off
of the Tendermint protocol. It works by separating time units into voting periods. In each
voting period, a validator (the equivalent of a miner in proof of work) proposes a new 
block and all the other validators vote on whether to  accept that block. A new block 
is only appended to the blockchain once it gains at least 2/3 of votes.

[Reach goal] PoS_Blockchain.als: *Sort of working" Shows the Proof of Stake protocol in
a blockchain and punishment protocol for users that double spend. Instead of computational
power, adding a block to the blockchain is based on a user's money (or "stake") at a 
specific time. Has a fraudulent block that has two repeating transactions 
("double spending"). When a user attempts to add the block to the blockchain, their money 
will go to 0.  

---------------------------------Abstraction Choices You Made---------------------------------

Key Exchange:

Alice, Bob, Eve and the Server are abstracted out to be User sigs because they all require
common features (a contact list, private/public keys, etc) and are able to perform the similar
actions (send messages).

Keys, nonces, user requests are all abstracted out to be sendable values because each message
can have a payload that represents different things (some messages contain user info,
others nonces, others have proof of decoded nonces).


---------------------------------Outcomes your Model can Show --------------------------------

Keys: Our model can show normal key exchange, the MitM attack with Eve and the fixed version
of MitM. 

---------------------------------------Difficulties-------------------------------------------

We experienced problems with buffer overflow as alloy continually gave us a negative value when
we used the #{} count operator. We fixed this by increasing the scope of the Int in alloy to a 
higher bit width.

It was also difficult to figure out the exact number we needed for each sig when we tried to run
our model. We ended up testing different values until it all worked. 

It was also hard to reconcile alloy’s limitations, especially in regards to scope. We ended up 
discarding a lot of the content that wasn’t necessary for demonstrating the main problems in the 
model, such as the man-in-the-middle attack in the key exchange and the 51% attack in the
blockchain model, even though the extra content exists in reality. 

Alloy also is unable to have probabilities and random values specified so we had to use a
work around and base out probabilities for proof of work on the any values within a certain
range depending on number of blocks. 

--------------------------------------------------------------------------------------------



quu..__
 $$$b  `---.__
  "$$b        `--.                          ___.---uuudP
   `$$b           `.__.------.__     __.---'      $$$$"              .
     "$b          -'            `-.-'            $$$"              .'|
       ".                                       d$"             _.'  |
         `.   /                              ..."             .'     |
           `./                           ..::-'            _.'       |
            /                         .:::-'            .-'         .'
           :                          ::''\          _.'            |
          .' .-.             .-.           `.      .'               |
          : /'$$|           .@"$\           `.   .'              _.-'
         .'|$u$$|          |$$,$$|           |  <            _.-'
         | `:$$:'          :$$$$$:           `.  `.       .-'
         :                  `"--'             |    `-.     \
        :##.       ==             .###.       `.      `.    `\
        |##:                      :###:        |        >     >
        |#'     `..'`..'          `###'        x:      /     /
         \                                   xXX|     /    ./
          \                                xXXX'|    /   ./
          /`-.                                  `.  /   /
         :    `-  ...........,                   | /  .'
         |         ``:::::::'       .            |<    `.
         |             ```          |           x| \ `.:``.
         |                         .'    /'   xXX|  `:`M`M':.
         |    |                    ;    /:' xXXX'|  -'MMMMM:'
         `.  .'                   :    /:'       |-'MMMM.-'
          |  |                   .'   /'        .'MMM.-'
          `'`'                   :  ,'          |MMM<
            |                     `'            |tbap\
             \                                  :MM.-'
              \                 |              .''
               \.               `.            /
                /     .:::::::.. :           /
               |     .:::::::::::`.         /
               |   .:::------------\       /
              /   .''               >::'  /
              `',:                 :    .'
                                   `:.:' 

Filled with po-key-mon fun! Feed us some poke-blockchains. 
