package view;

import java.util.List;
import java.util.Scanner;

import controller.Client;
import model.TowerCoordinates;


public class ClientTUI {
	private Client client;
	private Scanner scanny;
	
	/**
	 * Constructs a new TUI for a client.
	 * @param client Client the TUI belongs to.
	 */
	public ClientTUI(Client client) { 
		this.client = client;
		scanny = new Scanner(System.in);
	} 
	
	/**
	 * Starts the TUI with the startMenu.
	 */
	public void start() {
		System.out.println("Hello");
		startMenu();
	}
	
	/**
	 * Start Menu which is called at the beginning and at after a game finished.
	 */
	public void startMenu() {
		System.out.println("Please enter you input: \n"
				+ " - Play for Play a 4-wins game. \n"
				+ " - Help for additionnal information\n"
				+ " - Exit for terminating the application");
		boolean play = false;
		while (!play) {
			if (scanny.hasNext()) {
				String input = scanny.next();
				switch (input) {
					case "Help":
						helpMenu();
						break;
					case "Play":
						client.playMenu();
						play = true;
						break;
					case "Exit":
						client.terminateMenu();
						play = true; 
						break;
					default:
						errorMessage(6);
				}
			}
		}		
	}
	
	/**
	 * Prints the given message on the Terminal.
	 * @param message Message to print.
	 */
	public void printMessage(String message) {
		System.out.println(message);
	}
	
	/**
	 * Asks the user for the next move and returns its tower coordinates.
	 * @param prompt Message to print on the screen.
	 * @return tower Coordinates for the next move.
	 */

	//TODO check it.
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
					TowerCoordinates coord = client.determineHint();
					System.out.println("This move is suggested: \n x = "
							+ coord.getX() + "\n y = " + coord.getY());
					validMove = readBoolean("Do you want to play this move?", "yes", "no");
					if (validMove) { 
						return coord;
					}
				}
			}
		}
		return null;	
	}
	
	/**
	 * Prints the situation of the current board, after a move has been made.
	 * @param observable Observable object that notified the TUI.
	 * @param boardData Data of the board (observable object)
	 */
	//TODO check boundaries / representation
	public void printBoard(List<List<Integer>> boardData, int x, int y, int z, int id) {
		for (int k = 0; k < z; k++) {
			System.out.println("\nLevel " + (k + 1) + "\n");
			for (int j = 0; j < y; j++) {
				System.out.println(drawLine(id, x));
				System.out.println(dashedLine(id, x));
				StringBuilder cells = new StringBuilder();
				for (int h = 0; h < x; h++) {
					cells.append("|   " + boardData.get(h).get(j) + "   ");
				}
				cells.append("|");
				System.out.println(cells.toString());
				System.out.println(dashedLine(id, x));
			}
			System.out.println(drawLine(id, x));
		}
	}
	
	/**
	 * Returns a line (___) as String.
	 * @param amount Amount of players playing, determines how big each interval should be.
	 * @param times Amount of x cells of the board.
	 * @return the finished line.
	 */
	//@ requires amount >= 0 && times > 0;
	//TODO amount /10 not working yet.
	public String drawLine(int amount, int times) {
		String part = "";
		int idLength = (int) (Math.log10(amount) + 1);
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
	//@ requires amount >= 0 && times > 0;
	public String dashedLine(int amount, int times) {
		String part = "|";
		int idLength = (int) (Math.log10(amount) + 1);
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
						errorMessage(6);
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
						errorMessage(6);
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
				+ " - Randi for a player with Random strategy\n");
		while (true) {
			if (scanny.hasNextLine()) {
				strategy = scanny.nextLine();
				switch (strategy) {
					case  "Randi":
						return "Randi";
					default:
						errorMessage(7);
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
	
	/**
	 * The method asks the client for a valid integer (positive integer).
	 * @return entered dimension.
	 */
	//@ensures \result >=1;
	public int getInt(String message) {
		System.out.println(message);
		int x = -1;
		while (x < 1) {
			if (scanny.hasNextInt()) {
				x = scanny.nextInt();
				if (x < 1) {
					System.out.println("Please enter a positive integer: ");
				}
			} else if (scanny.hasNext()) {
				scanny.next();
				System.out.println("Please enter an integer: ");
			} 
		}
		return x;
	}
	
	//<<----------- Methods needed by determine Move ------------>>
	
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

	// <<---------- Methods to transfer messages -------->>
	/**
	 * Successfull messages.
	 * @param type
	 */
	public void valid(int type) {
		switch (type) {
			case 1:
				System.out.println("Socket created");
				break;
			default:
				break;
		}
	}
	
	/**
	 * Prints the error message.
	 * @param type what kind of message should be printed.
	 */
	//TODO work with enum.
	public void errorMessage(int type) {
		switch (type) {
			case 1:
				System.out.println("Invalid address name.\n");
				break;
			case 2:
				System.out.println("Invalid Port number.\n");
				break;
			case 3: 
				System.out.println("Problem while disconnecting.\n");
				break;
			case 4:
				System.out.println("Invalid coordinates.\n");
				break;
			case 5:
				System.out.println("The socket connection failed. You return to the start menu.\n");
				startMenu();
				break;
			case 6:
				System.out.println("Invalid input\n");
				break;
			case 7:
				System.out.println("Not a valid Strategy.\n");
				break;	
			case 8: 
				System.out.println("The Stream connection failed.\n");
				break;
			case 9:
				System.out.println("Problems while communicating with the server.\n");
				break;
			case 10: 
				System.out.println("You return to the start menu.\n");
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

}
