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

[Foundation goal] Blockchain.als: Demonstrates forking, block addition to a blockchain and 
proof of work where no one miners has a computational advantage over other miners. 

[Target goal] EvilMiner.als: Demonstrates a 51% attack where one miner has over 51% 
of the computational power.

[Reach goal] BFT_Blockchain.als: Demonstrates Byzantine fault tolerance with a consensus
based block addition based off of the Tendermint protocol. Instead of adding a block based
on computational power (proof of work), a block is proposed by one of the validators and
is voted on. When a 2/3 consensus is reached, the block is added to the blockchain.

[Reach goal] PoS_Blockchain.als: *Sort of working" Shows the Proof of Stake protocol in
a blockchain and punishment protocol for users that double spend. Instead of computational
power, adding a block to the blockchain is based on a user's money (or "stake") at a 
specific time. Has a fraudulent block that has two repeating transactions 
("double spending"). When a user attempts to add the block to the blockchain, their money 
will go to 0.  

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