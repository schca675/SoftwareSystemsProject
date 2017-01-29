package view;

import java.util.List;
import java.util.Observable;
import java.util.Scanner;

//import client.Client;
import model.TowerCoordinates;


public class ClientTUI extends Observable {
	private Scanner scanny;
	
	/**
	 * Constructs a new TUI for a client.
	 * @param client Client the TUI belongs to.
	 */
	public ClientTUI() { 
		scanny = new Scanner(System.in);
	} 
	
	/**
	 * Starts the TUI with the startMenu.
	 */
	public void start() {
		System.out.println("Hello");
	}
	
	/**
	 * Start Menu which is called at the beginning and at after a game finished.
	 */
	public String startMenu() {
		System.out.println("\nPlease enter you input: \n"
				+ " - Play for Play a 4-wins game. \n"
				+ " - Help for additionnal information\n"
				+ " - Exit for terminating the application");
		while (true) {
			if (scanny.hasNext()) {
				return scanny.next();
			}
		}		
	}
	
	/**
	 * Asks the user for the next move and returns its tower coordinates.
	 * @param prompt Message to print on the screen.
	 * @return tower Coordinates for the next move.
	 */
	public TowerCoordinates determineMove() {
		boolean validMove = false;
		while (!validMove) {
			System.out.println("Please enter the coordinates of"
					+ " your next move or write \"Hint\" to get a suggested move");
			if (scanny.hasNextInt()) {
				String format = "Please write the coordinates in this form: x y";
				return readCoordinates(format);
			} else if (scanny.hasNext()) {
				String input = scanny.next();
				if (input.equals("Hint")) {
					setChanged();
					notifyObservers("Hint");				
				}
			}
		}
		return null;	
	}
	
	/**
	 * Print the model of the board, whit the indices to be used.
	 * @param xmax
	 * @param ymax
	 */
	public void printModel(int xmax, int ymax) {
		System.out.println("Model of the board:\nThe indices are as follows:");
		int middleLength = digitLength(xmax) + 1 /*space*/ + digitLength(ymax);
		String format = "%" + middleLength + "s";
		for (int x = 1; x <= xmax; x++) {
			System.out.println(drawLine(middleLength, ymax));
			System.out.println(dashedLine(middleLength, ymax));
			StringBuilder cells = new StringBuilder();
			for (int y = 1; y <= ymax; y++) {
				String cell = x + " " + y;
				cells.append("|   " + String.format(format, cell) + "   ");
			}
			cells.append("|");
			System.out.println(cells.toString());
			System.out.println(dashedLine(middleLength, ymax));
		}
		System.out.println(drawLine(middleLength, ymax));
	}
	
	/**
	 * Prints the situation of the current board, after a move has been made.
	 * @param observable Observable object that notified the TUI.
	 * @param boardData Data of the board (observable object)
	 */
	public void printBoard(List<List<Integer>> boardData, int xmax, int ymax, int zmax, int id) {
		for (int z = 0; z < zmax; z++) {
			System.out.println("\nLevel " + (z + 1) + "\n");
			for (int x = 0; x < xmax; x++) {
				System.out.println(drawLine(digitLength(id), ymax));
				System.out.println(dashedLine(digitLength(id), ymax));
				StringBuilder cells = new StringBuilder();
				for (int y = 0; y < ymax; y++) {
					int index = x + y * xmax;
					if (boardData.get(index).size() < z + 1) {
						cells.append("|   " + printMiddle(digitLength(id)) + "   ");
					} else {
						cells.append("|   " + boardData.get(index).get(z) + "   ");
					}
				} 
				cells.append("|");
				System.out.println(cells.toString());
				System.out.println(dashedLine(digitLength(id), ymax));
			}
			System.out.println(drawLine(digitLength(id), ymax));
		}
	}
	
	/**
	 * Returns a line (___) as String.
	 * @param amount Amount of players playing, determines how big each interval should be.
	 * @param times Amount of x cells of the board.
	 * @return the finished line.
	 */
	//@ requires idLength >= 0 && times > 0;
	public String drawLine(int idLength, int times) {
		String part = "";
		for (int i = 0; i < (idLength + 4 + 2); i++) {
			part = part + "-";
		}
		part = part + "+";
		StringBuilder line = new StringBuilder();
		line.append('+');
		for (int j = 0; j < times; j++) {
			line.append(part);
		}
		return line.toString();
	}
	
	/**
	 * Returns the dashed middle part of the board representation.
	 * @param amount Amount of players playing, determines how big each interval should be.
	 * @param times Amount of x cells of the board.
	 * @return the finished drawing element.
	 */
	//@ requires idLength >= 0 && times > 0;
	public String dashedLine(int idLength, int times) {
		String part = "|";
		for (int i = 0; i < (idLength + 4 + 2); i++) {
			part = part + " ";
		}
		StringBuilder line = new StringBuilder();
		for (int j = 0; j < times; j++) {
			line.append(part);
		}
		line.append('|');
		return line.toString();
	}
		
	/**
	 * Return the highest amount of digits of the player IDs.
	 * @param playerAmount amount of players playing.
	 * @return amount of digits.
	 */
	public int digitLength(int playerAmount) {
		return (int) (Math.log10(playerAmount) + 1);
	}
	
	/**
	 * Print the middle in case there is no entry yet.
	 * @param amount
	 * @return
	 */
	public String printMiddle(int idLength) {
		String result = "";
		for (int i = 1; i <= idLength; i++) {
			result = result + " ";
		}
		return result;
	}
	// <<------- Menus called by the StartMenu ---------->>
	/**
	 * Prints additional information for the game.
	 */
	public void helpMenu() {
		System.out.println("The game consist of a three dimensional board and "
				+ "has to be played by at least 2 players.\n"
				+ "The default dimensions are 4x4x4 with a winning length of 4\n"
				+ "However it is also possible to enter own dimensions.\n"
				+ "You can play on your own or let a Computer Player play for you.\n\n"
				+ "To play, the program is connecting to a server to find opponents.");
	}
	
	/**
	 * Terminates the TUI.
	 */
	public void terminateMenu() {
		System.out.println("Goodbye!");
		scanny.close();
	}
	
	// <<---- Methods used by the client's play Menu ----->>
	
	/**
	 * Determines if the user wants to play as human or as Computerplayer.
	 * Depending on the answer, the TUI asks the Client to create the respective player.
	 * @return true if the user wants to play as Human and 
	 * false if he wants to let the Computer play.
	 */
	public boolean determinePlayer() {
		System.out.println("Do you want to play as on your own or let a Computer player play?\n"
				+ " - Human for Human Player\n"
				+ " - Com for Computer Player");
		while (true) {
			if (scanny.hasNext()) {
				String input = scanny.next();
				switch (input) {
					case "Human":
						return true;
					case "Com":
						return false;
					default:
						errorMessage(MessageType.INVALID_INPUT);
				}
			}
		}
	}
	
	/**
	 * Determines if the player wants to play with default or own dimensions.
	 */
	public boolean determineDimensions() {
		System.out.println("With which dimensions do you want to play?\n"
				+ " - Def for default dimensions (4x4x4)\n"
				+ " - Own for own dimensions ");
		while (true) {
			if (scanny.hasNext()) {
				String input = scanny.next();
				switch (input) {
					case "Def":
						return true;
					case "Own":
						return false;
					default:
						errorMessage(MessageType.INVALID_INPUT);
				}
			}
		}
	}
	
	/**
	 * Asks for an Internet address to connect to.
	 * @return Internet address.
	 */
	public String getInetAddress() {
		return getString("Please enter a Internet Address you want to connect to (String)");
	}
	
	/**
	 * Asks for a port number to connect to.
	 * @return port number.
	 */
	public int getPort() {
		return getInt("Please enter a port number (between 1000 an 65535)");
	}
	
	// <<------- Method needed by determinePlayer ----------->>
	/**
	 * The method asks for the user's player's name.
	 * @return
	 */
	public String determinePlayerName() {
		String name;
		System.out.println("Write your player's name:");
		while (true) {
			if (scanny.hasNextLine()) {
				name = scanny.nextLine();
				if (!name.equals("")) {
					return name;
				}
			}
		}
	}
	
	/**
	 * The method asks with which strategy the user's Computerplayer should play.
	 * It does not check if the given strategy exists.
	 */
	public String determineStrategy() {
		String strategy;
		System.out.println("Please name the Computer should play with:\n"
				+ "The following are implemented:\n"
				+ " - Randi for a player with Random strategy\n"
				+ " - Trams for a player with Smart strategy (takes winning move if "
				+ "possible, else a random move)\n");
		while (true) {
			if (scanny.hasNextLine()) {
				strategy = scanny.nextLine();
				switch (strategy) {
					case  "Randi":
						return "Randi";
					case "Trams":
						return "Trams";
					default:
						errorMessage(MessageType.INVALID_STRATEGY);
						break; 
				}
			}
		}
	}
	
	// <<---------- Methods needed for determineDimensions ------- >>

	/**
	 * Asks the specific x dimension.
	 * @return X Dimension.
	 */
	//@ ensures \result >= 1;
	public int getXDimension() {
		return getInt("Please enter the x dimension (integer): ");
	}
	
	/**
	 * Asks the specific Y dimension.
	 * @return Y Dimension.
	 */
	//@ ensures \result >= 1;
	public int getYDimension() {
		return getInt("Please enter the y dimension (integer): ");
	}
	
	/**
	 * Asks the specific Z dimension.
	 * @return Z Dimension.
	 */
	//@ ensures \result >= 1;
	public int getZDimension() {
		return getInt("Please enter the z dimension (integer): ");
	}
	
	/**
	 * Asks the specific winning length.
	 * @return Winning Length.
	 */
	//@ ensures \result >= 1;
	public int getWinDimension() {
		return getInt("Please enter the winning length (integer): ");
	}
	
	/**
	 * Displays the dimensions, the program tries to open a game with.
	 * @param x X dimension
	 * @param y Y dimension
	 * @param z Z dimension
	 * @param win Winning length
	 */
	public void displayDimensions(int x, int y, int z, int win) {
		System.out.println("The dimensions are: \n - "
				+ x + " for the x dimension\n - "
				+ y + " for the y dimension\n - "
				+ z + " for the z dimension\n - "
				+ win + " for the winning length.\n");
	}

	// <<---------- Methods to transfer messages -------->>
	
	/**
	 * Print a message on the Terminal.
	 * @param message Message to print.
	 */
	public void print(String message) {
		System.out.println(message);
	}
	
	/**
	 * Successfull messages.
	 * @param type Type of successfull message.
	 */
	public void valid(MessageType type) {
		switch (type) {
			case SOCKET_CREATED:
				System.out.println("Socket created\n");
				break;
			case GOT_SERVER_CAP:
				System.out.println("The server capabilities are received.\n");
				break;
			case SENT_CLIENT_CAP:
				System.out.println("The client capabilities are sent.\n");
				break;
			case GOT_ID:
				System.out.println("The client ID is received.\n");
				break;
			case GAME_START: 
				System.out.println("The game starts.\n");
				break;
			case MOVE_MADE:
				System.out.println("A move is made.\n");
				break;
			default:
				break;
		}
	}
	
	/**
	 * Prints the error message.
	 * @param type what kind of message should be printed.
	 */
	public void errorMessage(MessageType type) { 
		switch (type) {
			case INVALID_ADDRESS:
				System.out.println("Invalid address name.\n");
				break;
			case INVALID_PORT:
				System.out.println("Invalid Port number.\n");
				break;
			case PROBLEM_DISCONNECTING: 
				System.out.println("Problem while disconnecting.\n");
				break;
			case INVALID_COORDINATES:
				System.out.println("Invalid coordinates.\n");
				break;
			case SOCKET_FAILURE:
				System.out.println("The socket connection failed. You return to the start menu.\n");
				break;
			case INVALID_INPUT:
				System.out.println("Invalid input\n");
				break;
			case INVALID_STRATEGY:
				System.out.println("Not a valid Strategy.\n");
				break;	
			case STREAM_FAILURE: 
				System.out.println("The Stream connection failed.\n");
				break;
			case WRITING_FAILURE:
				System.out.println("Problems while writing to the server.\n");
				break;
			case RETURN_START: 
				System.out.println("You return to the start menu.\n");
				break;
			case SERVER_LISTENING:
				System.out.println("Problems while listening to the server\n");
				break;
			case PROTOCOL_IRREGULARITIES:
				System.out.println("Protocol irregularities\n");
				break;
			case SERVER_ILLEGAL_MOVE:
				System.out.println("Server sent an illegal move.\n");
				break;
			default:
				break;
		}
	}
	
	
	// <<--------- Request input methods ------------->>
	/**
	 * Determines whether the user enters Yes or No.
	 * @param message Message to print on the screen.
	 * @param yes String that should be interpreted as "yes".
	 * @param no String that should be interpreted as "no".
	 * @return true or false, depending on the input of the user.
	 */
	public Boolean readBoolean(String message, String yes, String no) {
		Boolean compared = false;
		Boolean result = null;
		String scanned = "";
		System.out.println(message);
		while (!compared) {
			System.out.println("Please answer in the format (" + yes + "/" + no + ") : " 
					+ yes + " for yes or " + no + " for no");
			if (scanny.hasNext()) {
				scanned = scanny.next();
				if (scanned.equals(yes)) {
					result = true;
				} else if (scanned.equals(no)) {
					result = false;
				}
			}
			if (result != null) {
				compared = true;
			}
		}
		return result;
	}
	
	/**
	 * The method asks the client for a valid integer:
	 * positive integer or -1 for unlimited dimension.
	 * @return entered dimension.
	 */
	//@ensures \result >=0;
	public int getInt(String message) {
		System.out.println(message);
		int x = -2;
		while (x < 0) {
			if (scanny.hasNextInt()) {
				x = scanny.nextInt();
				if (x < 0) {
					System.out.println("Please enter a positive integer  (0 "
							+ "for unlimited size: ");
				}
			} else if (scanny.hasNext()) {
				scanny.next();
				System.out.println("Please enter an integer: ");
			} 
		}
		return x;
	}
	
	/**
	 * Reads the coordinates provided by the user.
	 * It only ensures the coordinates are indeed integers, not if they are valid towers.
	 * 
	 * @param message Message that should be printed.
	 * @return Coordinates that the player entered.
	 */
	// checked
	public TowerCoordinates readCoordinates(String format) {
		int x = -1;
		int y = -1;
		int countInt = 0;
		// read until getting two integers.
		while (countInt != 2) {
			if (scanny.hasNextLine()) {
				Scanner integers = new Scanner(scanny.nextLine());
				while (countInt < 2 && integers.hasNextInt()) {
					if (countInt == 0) {
						x = integers.nextInt();
					} else if (countInt == 1) {
						y = integers.nextInt();
					}
					countInt = countInt + 1;
				}
				integers.close();
				if (countInt != 2) {
					countInt = 0;
					System.out.println(format);
				}
			}		
		}
		return new TowerCoordinates(x, y);
	}
	
	/**
	 * Gets a string from the Terminal.
	 * @param message message to write on the Terminal
	 * @return Line entered by the user.
	 */
	public String getString(String message) {
		System.out.println(message);
		while (true) {
			if (scanny.hasNext()) {
				return scanny.next();
			}
		}
	}

}
