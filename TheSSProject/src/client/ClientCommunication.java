package client;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Observable;
import java.util.Observer;

import exc.IllegalBoardConstructorArgumentsException;
import exc.IllegalCoordinatesException;
import exc.InvalidSyntaxException;
import exc.TowerCoordinates;
import model.Board;
import model.ComputerPlayer;
import model.Player;
import model.Strategy;
import view.ClientTUI;

public class ClientCommunication implements Observer, Runnable {
	//<<------- Variables needed for a play -------->>
	private Player me;
	private String name;
	private Strategy strategy;
	private List<Player> players;
	private Board board;
	private boolean playing;
	private Client client;
	private ComputerPlayer hintGiver;
	
	private ClientTUI view;
	
	// <<---- Variables needed for communication to server --------->>
	private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;
	
	// <<-------- Constants needed for the protocol ----------->>
	
	public static final int DEFAULTPLAYERSIZE = 2;
	public static final int UNLIMITEDSIZE = 20;
	public static final int UNLIMITEDPLAYERS = 4;
	public static final int FALSE = 0;
	public static final int TRUE = 1;
	
	// < -------- Server to Client messages ----------->
	public static final String SERVERCAPABILITIES = "serverCapabilities";
	public static final String SENDLISTROOMS = "sendListRooms";
	public static final String ASSIGNID = "assignID";
	public static final String STARTGAME = "startGame";
	public static final String TURNOFPLAYER = "playerTurn";
	public static final String NOTIFYMOVE = "notifyMove";
	public static final String NOTIFYEND = "notifyEnd";
	public static final String ERROR = "error";
	public static final String NOTIFYMESSAGE = "notifyMessage";
	public static final String SENDLEADERBOARD = "sendLeaderBoard";
	
	// < --------- Client to server messages --------------->
	public static final String SENDCAPABILITIES = "sendCapabilities";
	public static final String JOINROOM = "joinRoom";
	public static final String GETROOMLIST = "getRoomList";
	public static final String LEAVEROOM = "leaveRoom";
	public static final String MAKEMOVE = "makeMove";
	public static final String SENDMESSAGE = "sendMessage";
	public static final String REQUESTLEADERBOARD = "requestLeaderboard";
	
	/**
	 * Creates a new Client Communication thread.
	 * @param socket Socket the thread should listen to.
	 * @param view TUI of the client.
	 * @throws IOException in case the streams can not be initialized.
	 */
	public ClientCommunication(Socket socket, ClientTUI view, String name, Strategy strategy,
			Client client) throws IOException {
		this.view = view;
		this.socket = socket;
		this.client = client;
		in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
		this.name = name;
		this.strategy = strategy;
		me = null;
		playing = false;
		board = null;
		players = new ArrayList<Player>();
	}
	
	/**
	 * Constructor needed for testing purposes.
	 * @param name name of player.
	 */
	
	public ClientCommunication(ClientTUI view, String name) {
		this.view = view;
		this.name = name;
	}
	
	/**
	 * Starts the ClientCommunication thread.
	 */
	public void run() {
		listen();
	}
	
	/**
	 * Listens to the incoming messages of the InputStream.
	 */
	public void listen() {
		String message;
		try { 
			message = in.readLine();
			react(message);
		} catch (IOException | NullPointerException e) {
			disconnect();
		}
	}
	
	/**
	 * Reacts to the incoming messages by the protocol and calls the corresponding methods.
	 */
	public void react(String input)  {
		String[] message = input.split(" ");
//		 to be deleted.
//		for (int i = 0; i < message.length; i++){
//			System.out.println(i + " : " + message[i]);
//		}
		if (message.length >= 1) {
			switch (message[0]) {
				case SERVERCAPABILITIES:
					try {
						if (message.length == 8) {
							String answer = serverCapabilities(message);
							write(answer);
						}
					} catch (InvalidSyntaxException | NumberFormatException e) {
						view.errorMessage(12);
						disconnect();
					}
					break;
				case ASSIGNID:
					try {
						if (message.length == 2) {
							
							int id = Integer.parseInt(message[1]);
							makeMe(name, strategy, id);
						}
					} catch (NumberFormatException e) {
						view.errorMessage(12);
						disconnect();
					}
					break;
				case STARTGAME:
					// There have to be at least 2 players
					if (message.length >= 4) {
						try {
							makeBoard(message[1]);
							String[] playersString = new String[message.length - 2];
							System.arraycopy(message, 2, playersString, 0, message.length - 2);
							players = makePlayers(playersString);
							if (me != null) {
								playing = true;
							} else {
								view.errorMessage(12);
								disconnect();
							}
						} catch (InvalidSyntaxException | IllegalBoardConstructorArgumentsException 
								| NumberFormatException e) {
							view.errorMessage(12);
							disconnect();
						}	
					} else {
						view.errorMessage(12);
						disconnect();
					}
					break;
				case TURNOFPLAYER:
					// Should not be received if no game is on.
					if (playing && message.length == 2) {
						try {
							int current = Integer.parseInt(message[1]);
							if (current == me.playerID) {
								TowerCoordinates play = determineMove();
								if (play != null) {
									String answer = sendCoordinates(play);
									write(answer);
								} else {
									// either the board or the "me" player is not initialized. 
									// Theoretically impossible.
									view.errorMessage(12);
									disconnect();
								}
							}
							// else do nothing and listen until server sends NotifyMove.
						} catch (NumberFormatException e) {
							view.errorMessage(12);
							disconnect();
						}
					} else {
						view.errorMessage(12);
						disconnect();
					}
					break;
				case NOTIFYMOVE:
					// Should not be received if no game is on.
					if (playing && message.length == 4) {
						try {
							int id = Integer.parseInt(message[1]);
							int x = Integer.parseInt(message[2]);
							int y = Integer.parseInt(message[3]);
							makeMove(x, y, id);
						} catch (NumberFormatException e) {
							view.errorMessage(12);
							disconnect();
						}
					} else {
						view.errorMessage(12);
						disconnect();
					}
					break;
				case NOTIFYEND:
					// Should not be received if no game is on.
					if (playing && message.length >= 2) {
						try {
							int reason = Integer.parseInt(message[1]);
							int id = -1;
							String result = "";
							if (reason == 1 && message.length == 3) {
								id = Integer.parseInt(message[2]);
								result = determineEnd(reason, id);
							} else {
								result = determineEnd(reason);
							}
							view.print(result);
						} catch (NumberFormatException e) {
							view.errorMessage(12);
							disconnect();
						}
					} else {
						view.errorMessage(12);
						disconnect();
					}
					break;
				case ERROR:
					if (message.length == 2) {
						String type = message[1];
						String error = getError(type);
						view.print(error);
					}
					break;
				default:
					break;
			}
			listen();
		} else {
			//TODO
			view.errorMessage(12);
			disconnect();
		}		
	}
	
	/**
	 * The method sends messages to the server, writes to the output Stream.
	 * @param message message to communicate to the server.
	 */
	public void write(String message) {
		try {
			out.write(message);
		} catch (IOException e) {
			view.errorMessage(9);
			disconnect();
		}
	}
	
	/**
	 * Disconnect from the server. 
	 * Either because of an error detected in the protocol, or after the game finished.
	 */
	public void disconnect() {
		try {
			out.close();
			in.close();
			socket.close();
		} catch (IOException | NullPointerException e) {
			view.errorMessage(3);
		}
	}
	
	//<<------- Reactions ------------>>
	
	/**
	 * Interpretes the serverCapabilities message of the server.
	 * @param message message by the server.
	 * @return answer of the client.
	 * @throws InvalidSyntaxException thrown when the syntax of the protocol does not hold.
	 */
	//@ requires message.length == 8;
	public String serverCapabilities(String[] message) throws InvalidSyntaxException {
		int amount = Integer.parseInt(message[1]);
		boolean room = giveBoolean(message[2]);
		int maxX = Integer.parseInt(message[3]);
		int maxY = Integer.parseInt(message[4]);
		int maxZ = Integer.parseInt(message[5]);
		int maxWin = Integer.parseInt(message[6]);
		boolean chat = giveBoolean(message[7]);
		return sendClientCapabilities(amount, room, maxX, maxY, maxZ, maxWin, chat);
	}
	
	/**
	 * Creates a sending the client's capabilities message according to the protocol.
	 * @param amountPlayers Amount of players the server can deal wwith in one game.
	 * @param roomSupport whether the server can handle rooms o not.
	 * @param maxX maximal X dimension the server can handle.
	 * @param maxY maximal Y dimension the server can handle.
	 * @param maxZ maximal Z dimension the server can handle.
	 * @param maxWin maximal winning length the server can handle.
	 * @param chat whether the server is able to use chat or not.
	 * @return reaction message with the client's capabilities.
	 */
	public String sendClientCapabilities(int amountPlayers, boolean roomSupport, 
			int maxX, int maxY, int maxZ, int maxWin, boolean chat) {
		StringBuilder result = new StringBuilder();
		result.append(SENDCAPABILITIES);
		result.append(" ");
		// add the amount of players the client and the server can deal with.
		if (amountPlayers == DEFAULTPLAYERSIZE) {
			result.append(DEFAULTPLAYERSIZE);
		} else {
			result.append(UNLIMITEDPLAYERS);
		}
		result.append(" ");
		// add player name, cannot contain spaces.
		if (name.contains(" ")) {
			name.replaceAll(" ", "_");
		}
		result.append(name);
		result.append(" ");
		// add if client can support rooms, which this client cannot.
		result.append(FALSE);
		result.append(" ");
		// add the dimensions x, y, z and the winning length.
		// since our program can handle illimitated dimensions, we return the same as the server.
		result.append(maxX);
		result.append(" ");
		result.append(maxY);
		result.append(" ");
		result.append(maxZ);
		result.append(" ");
		result.append(maxWin);
		result.append(" ");
		// add chat Support, which is not enabled on this client
		result.append(FALSE);
		result.append(" ");
		// add autoRefresh function, which is not implemented on this client.
		result.append(FALSE);
		return result.toString();
	}
	
	/**
	 * Transfers the coordinates of the next move into a format that can be sent to the server.
	 * @param move Move the user desires to make.
	 * @return Command together with the string representation of the move.
	 */
	public String sendCoordinates(TowerCoordinates move) {
		return MAKEMOVE + " " + move.getX() + " " + move.getY();
	}
	
	/**
	 * Create the user's player.
	 * @param meName name of the user's player.
	 * @param meID id of the user's player.
	 */
	public void makeMe(String meName, Strategy meStrategy, int meID) {
		if (meStrategy != null) {
			me = new ComputerPlayer(meStrategy, meID);
		} else if (meName != null) {
			me = new Player(meName, meID);
		}
	}
	
	/**
	 * Creates a board from the dimensions given as input. 
	 * The client Communication thread saves this board.
	 * @param dimensions String containing the dimensions.
	 * @return Copy of the board the client should play on.
	 * @throws InvalidSyntaxException in case not all the dimensions are indicated in the string.
	 * @throws IllegalBoardConstructorArgumentsException in case the server 
	 * sends invalid dimensions to create a board.
	 * @throws NumberFormatException in case the dimensions are not represented as integer.
	 */
	public Board makeBoard(String dimensions) throws InvalidSyntaxException, 
		IllegalBoardConstructorArgumentsException, NumberFormatException {
		String[] dims = dimensions.split("|");
		if (dims.length == 7) {
			int x = Integer.parseInt(dims[0]);
			int y = Integer.parseInt(dims[2]);
			int z = Integer.parseInt(dims[4]);
			int win = Integer.parseInt(dims[6]);
			board = new Board(x, y, z, win);
			// This is the observer in case the board makes a move
			board.addObserver(this);
			return board.deepCopy();
		} else {
			throw new InvalidSyntaxException(dimensions, " all the dimensions of the board");
		}
	}
	
	/**
	 * Creates a list of players from a String array 
	 * containing all the informations about the different players.
	 * @param input Array with all the players. Every element represents one player.
	 * @return List of all the players described in the input.
	 * @throws InvalidSyntaxException in case not all the information for a player are present.
	 * @throws NumberFormatException in case the player id is not an integer.
	 */
	public List<Player> makePlayers(String[] input) throws InvalidSyntaxException, 
		NumberFormatException {
		List<Player> result = new ArrayList<Player>();
		for (int i = 0; i < input.length; i++) {
			String[] details = input[i].split("\\|");
			if (details.length >= 2) {
				int id = Integer.parseInt(details[0]);
				String playerIName = details[1];
				//We do not use the colours for our implementation.
				Player playerI = new Player(playerIName, id);
				result.add(playerI);
			} else {
				throw new InvalidSyntaxException(input[i], "player");
			}
		}
		return result;
	}

	/**
	 * Determine boolean value out of a String.
	 * @param value String value representing the boolean.
	 * @return boolean the String represents.
	 * @throws InvalidSyntaxException in case the parameter string does not equal TRUE nor FALSE.
	 */
	public boolean giveBoolean(String value) throws InvalidSyntaxException {
		if (value.equals(String.valueOf(TRUE))) {
			return true;
		} else if (value.equals(String.valueOf(FALSE))) {
			return false;
		} else { 
			throw new InvalidSyntaxException(value, "boolean");
		} 

	}
	
	//<<----------- Game ------------ >>
	
	/** 
	 * Determines the next move to play, asks TUI in case of Human Player or the method of Computer
	 * Player, handles exceptions before server communication (local check).
	 * @return the TowerCoordinates the me-Player wants to play.
	 */
	public TowerCoordinates determineMove() {
		if (me != null && board != null) {
			if (me instanceof ComputerPlayer) {
				return ((ComputerPlayer) me).determineMove(board);
			} else {
				boolean valid = false;
				TowerCoordinates coord = new TowerCoordinates(-1, -1);
				while (!valid) {
					coord =  view.determineMove(); 
					if (coord != null && board.isValidMove(coord.getX(), coord.getY())) {
						valid = true;
					} else {
						view.errorMessage(4);
					} 
				}
				return coord;
			}
		} else {
			return null;
		}
	}
	
	/** 
	 * Makes the moves on the board, handles boards exception after getting the coordinates from 
	 * the server.
	 * @param x X Coordinate of the Tower, the player is playing.
	 * @param y Y Coordinate of the Tower, the player is playing.
	 * @param id ID of the player whose move it is.
	 */
	public void makeMove(int newX, int newY, int newID) {
		try {
			board.makeMove(newX, newY, newID);
		} catch (IllegalCoordinatesException e) {
			view.errorMessage(13);
			disconnect();
		}
	}
	
	/**
	 * Determine the type of end of the game.
	 * @param reason reason why the game ended.
	 * @param id player ID of the winner, in case of a win. 
	 * @return String stating the end.
	 */
	public String determineEnd(int reason, int id) {
		switch (reason) {
			case 1:
				return "Player " + id + " won the game";
			default:
				return determineEnd(reason);		
		}
	}
	
	/**
	 * Determine the type of end of the game. 
	 * @param reason reason why the game ended.
	 * @return String stating the end.
	 */
	public String determineEnd(int reason) {
		switch (reason) {
			case 1:
				return "There is a winner.";
			case 2:
				return "Board is full: Draw.";
			case 3:
				return "A player disconnected, the game stops. No winner.";
			case 4:
				return "Current player did not respond within the "
						+ "timeout, so the game stops. No winner";
			default:
				return "Unknown end situation";	
		}
	}
	
	// << --------- Observer pattern ------------>>
		/**
		 * After a change is made on the board, the client will alert the TUI 
		 * to print the changed situation.
		 * @param observable Board to observe.
		 * @param type Type of change the board has made.
		 */
	@Override
	public void update(Observable observable, Object type) {
		if (observable instanceof Board && type instanceof Integer) {
			Board playboard = (Board) observable;
			int id = 1;
			//id = players.size();
			id = 2;
			view.printBoard(playboard.deepDataCopy(), playboard.xDim, 
					playboard.yDim, playboard.zDim, id);
		} else if (observable instanceof ClientTUI && type.equals("Hint")) {
			hintGiver = new ComputerPlayer(me.playerID);
			TowerCoordinates coord = hintGiver.determineMove(board);
			view.print("This move is proposed: " + coord.toString());
		}
	}


	// <<------ Function provided by the protocol interface ----->>
	/**
	 * Function to get Error message by error code defined in protocol.
	 * @author Merel Meekes.
	 * @param number String with error code defined in Protocol
	 * @return Error explanation or null if invalid error code.
	 */
	public static String getError(String number) {
		String result = null;
		if (number.equals("1")) {
			result = "Client has not yet sent capabilities message, Server cannot proceed";
		} else if (number.equals("2")) {
			result = "Room sent in message joinRoom does not exist";
		} else if (number.equals("3")) {
			result = "The chosen room is no longer available, either it already filled up or was "
					+ "empty for too long";
		} else if (number.equals("4")) {
			result = "The input given by the client is not valid at this moment";
		} else if (number.equals("5")) {
			result = "The given move is not possible on this board";
		} else if (number.equals("6")) {
			result = "Client is not allowed to leave the room after the game has started";
		} else if (number.equals("7")) {
			result = "A message with piping in a wrong place was received";
		} else {
			result = "unknown error";
		}

		return result;
	}
}
