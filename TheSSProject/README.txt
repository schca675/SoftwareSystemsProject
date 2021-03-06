Software Systems Project 
Module 2
01/02/2017
FourWins Project
Jansen Erik - s1196014
Schmit Cathy - s1830929

------------------------------------------
Installation and execution:

Import the Project into Eclipse.
To use the program and play a FourWins game, first the server needs to be setup and only afterwards the Client can connect.

Setup of the Server:

Run the server class. Then the program asks for a port number on the console.
Enter a valid port number (Integer between 1025 and 65535). The program will only continue once a valid port number is entered.
Afterwards the server asks whether it should enable the extensions or not. Our implemented extension is a board with variable dimensions.
After this information is entered, the server starts listening and the clients can connect.

Setup of the client:

Run the client Class. The start menu of the client class gives you different options, to play, help, and exit the game. 
Exit terminates the application. Help prints the rule and some explanation of the game to the console. Play initiates to play a game.
To play a game the client needs some more information. First of all it asks whether the user wants to play by itself, give own moves 
in the game or if a Computer Player should play.
If the user wants to play by its own, a name has to be entered as next, if the user wants to let a Computer Player play, a strategy needs
to be entered.
After entering all these informations, the client asks to which IP address and port number it should connect. As soon
as valid inputs are given the client connects to the server and waits for a game to start.
The server does not initiate own clients, so to be able to simulate a game, at least two different clients need to be connected to the server.
As soon as two clients are connected, a new game is started and the server sends instructions.

Playing a game:

When a game is started the server notifies all the playing clients of which player needs to make the next move.
If it is the own client and the user wants to play by itself it is asked for input.
A hint functionality is given, so in case the user wants a hint it can just enter "Hint". 
The Hint is displayed, but the user still has to manually enter its desired move before it is executed.
During the whole game, the server is printing all the received and sent messages on the console.
When the server receives an invalid move the sending client is replaced by a Computer Player.

End of the game:
When the game ended, so either when there is a winner or when the board is full, the user gets informed about the situation.
The server disconnects the clients and continues listening to eventual clients that are connecting.
The disconnected client returns to the start menu and can start over by either exiting, calling help or playing a game.

------------------------------------
Special cases:

- In case the client receives invalid information of the server, it disconnects and returns to the start menu.
- The client can send three times invalid information before it disconnects the respective client. When using the application normally, 
  this case is not happening, because the client holds on to the protocol.
  
------------------------------------
System requirements:

This project was created in Eclipse by Laptops running on Windows 10.

------------------------------------
Error meaning written by the server

In case the server gets invalid messages from its clients it replies by sending error messages according to the numbering defined in the protocol.

Error message               |        explanation                    |       code
---------------------------------------------------------------------------------------
CapabilitiesNotSentYet      | Client has not yet sent capabilities  |   1
							| message, Server cannot proceed        |
---------------------------------------------------------------------------------------
InvalidMove                 | The given move is not possible on     |   4
							| this board							|
---------------------------------------------------------------------------------------
StringContainsIllegalChars  | For example a message with piping in  |   7
							| a wrong place was received            |
---------------------------------------------------------------------------------------

All the other errors in the protocol are not implemented because we did not implement Lobby or Chat functionalities.
