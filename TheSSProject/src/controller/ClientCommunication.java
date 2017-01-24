package controller;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.List;

import model.Board;
import model.ComputerPlayer;
import model.InvalidSyntaxException;
import model.Player;
import view.ClientTUI;

public class ClientCommunication extends Thread {
	private Player me;
	private String name;
	private ComputerPlayer hintGiver;
	private List<Player> players;
	private Board board;
	
	private ClientTUI view;
	
	// <<---- Variables needed for communication to server --------->>
	private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;
	
	// <<-------- Constants needed for the protocol ----------->>
	
	public static final int DEFAULTPLAYERSIZE = 2;
	public static final int ILLIMITATEDSIZE = 20;
	public static final int ILLIMITATEDPLAYERS = 4;
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
	 * Creates a new Client Communcation thread.
	 * @param socket Socket the thread should listen to.
	 * @param view TUI of the client.
	 * @throws IOException in case the streams can not be initialized.
	 */
	public ClientCommunication(Socket socket, ClientTUI view, String name) throws IOException {
		this.view = view;
		this.socket = socket;
		in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
		this.name = name;
	}
	/**
	 * Constructor needed for testing purposes.
	 * @param name name of player.
	 */
	
	public ClientCommunication(String name) {
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
		} catch (IOException e) {
			disconnect();
		}
	}
	
	/**
	 * Reacts to the incoming messages by the protocol and calls the corresponding methods.
	 */
	public void react(String input)  {
		String[] message = input.split(" ");
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
							me = new Player(name, id);
						}
					} catch (NumberFormatException e) {
						view.errorMessage(12);
						disconnect();
					}
					break;
				case STARTGAME:
					// There have to be at least 2 players
					if (message.length >= 4) {
						makeBoard(message[1]);
						String[] players = new String[message.length-2];
						System.arraycopy(message, 2, players, 0, message.length-2);
						makePlayers(players);
					}
					break;
				case TURNOFPLAYER:
					break;
				case NOTIFYMOVE:
					break;
				case NOTIFYEND:
					break;
				case ERROR:
					break;
				default:
					break;
			}
			listen();
		} else {
			//TODO
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
	
	public void disconnect() {
		try {
			out.close();
			in.close();
			socket.close();
		} catch (IOException e) {
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
		//TODO
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
			result.append(ILLIMITATEDPLAYERS);
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
	
	public Board makeBoard(String dimensions) {
		String[] dims = dimensions.split("|");
		if (length
		return null;
	}
	
	public boolean giveBoolean(String value) throws InvalidSyntaxException {
		if (value.equals(String.valueOf(TRUE))) {
			return true;
		} else if (value.equals(String.valueOf(FALSE))) {
			return false;
		} else { 
			throw new InvalidSyntaxException(value, "boolean" );
		} 

	}
	
}
