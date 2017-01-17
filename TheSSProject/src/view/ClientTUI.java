package view;

import java.util.List;
import java.util.Observable;
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
						playMenu();
						play = true;
						break;
					case "Exit":
						terminateMenu();
						play = true;
						break;
					default:
						System.out.println("Invalid input");
				}
			}
		}
	}
	
	/**
	 * Asks the user for the next move and returns its tower coordinates.
	 * @param prompt Message to print on the screen.
	 * @return tower Coordinates for the next move.
	 */
	// make a while loop in client which is only broken when the input given by the Tui 
	// does not throw an exception, could use 2 different Strings to print the message.
	public TowerCoordinates determineMove(String prompt) {
		System.out.println(prompt);
		String format = "Please write the coordinates in this form: x y";
		return readCoordinates(format);
	}
	
	/**
	 * Prints the situation of the current board, after a move has been made.
	 * @param observable Observable object that notified the TUI.
	 * @param boardData Data of the board (observable object)
	 */
	// check ? wild cards.
	public void update(Observable observable, Object boardData) {
		if (observable instanceof Client && boardData instanceof List<?>) {
			try {
				representation((List<List<Integer>>) boardData);
			} catch (ClassCastException e) {
				// TODO does it need to do sth?
			}
		}
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
	 * Initializes a game.
	 */
	public void playMenu() {
		//Determine if user is a computer or a human player 
		// and the client controller is creating a player.
		determinePlayer();
		//Determine if user wants to play with default or own dimensions 
		// and communicates it to the client controller.
		determineDimensions();
	}
	
	/**
	 * Terminates the TUI and the client.
	 */
	public void terminateMenu() {
		scanny.close();
		//TODO close the client etc as well.
	}
	
	// <<---- Methods used by the play Menu ----->>
	
	/**
	 * Determines if the user wants to play as human or as Computerplayer.
	 * Depending on the answer, the TUI asks the Client to create the respective player.
	 */
	public void determinePlayer() {
		System.out.println("Do you want to play as on your own or let a Computer player play?\n"
				+ " - Human for Human Player\n"
				+ " - Com for Computer Player");
		boolean chosen = false;
		while (!chosen) {
			if (scanny.hasNext()) {
				String input = scanny.next();
				switch (input) {
					case "Human":
						String name = determinePlayerName();
						//TODO let Client handle to create an appropriate player.
						chosen = true;
						break;
					case "Com":
						//strategy does not have to exist.
						String strategy = determineStrategy();
						chosen = true;
						//TODO let Client handle to create an appropriate player.
						break;
					default:
						System.out.println("Invalid input");
				}
			}
		}
	}
	
	public void determineDimensions() {
		System.out.println("With which dimensions do you want to play?\n"
				+ " - Def for default dimensions (4x4x4)\n"
				+ " - Own for own dimensions ");
		boolean chosen = false;
		while (!chosen) {
			if (scanny.hasNext()) {
				String input = scanny.next();
				switch (input) {
					case "Def":
						//TODO let client handle to remember to play with default board."
						chosen = true;
						break;
					case "Own":
						//TODO new function that determines valid dimensions from the user 
						//TODO let the board handle it.
						chosen = true;
						break;
					default:
						System.out.println("Invalid input");
				}
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
				+ " - Randi for a player with Random strategy");
		while (true) {
			if (scanny.hasNextLine()) {
				strategy = scanny.nextLine();
				if (!strategy.equals("")) {
					return strategy;
				}
			}
		}
	}
	
	// <<---------- Methods needed by determineDimensions ------- >>
	
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

	// <<---------- Methods needed by update -------->>
	public void representation(List<List<Integer>> data) {
		//TODO
	}
	// <<--------- Not needed methods yet ------------->>
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
