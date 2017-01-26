package testing;

import java.util.List;

import client.Client;
import client.ClientCommunication;
import exc.IllegalBoardConstructorArgumentsException;
import exc.InvalidSyntaxException;
import exc.TowerCoordinates;
import model.Board;
import model.Player;
import model.RandomStrategy;
import view.ClientTUI;

public class ClientCommunicationTest {

	/**
	 * Test all the client communication Class method which do not need a Server connection.
	 * @param args does not need any.
	 */
	public static void main(String[] args) {
		Client testClient = new Client();
		ClientTUI view = new ClientTUI(testClient);
		ClientCommunication client = new ClientCommunication(view, "Test");
		
		// Test the send Client capabilities 
		System.out.println("- Test the send Client's capabilities\n");
		String output = client.sendClientCapabilities(2, true, 5, 32, 4, 4, false);
		System.out.println(output);
		String[] input = new String[8];
		input[0] = "serverCapabilities";
		input[1] = "3";
		input[2] = "0";
		input[3] = "0";
		input[4] = "3";
		input[5] = "3"; 
		input[6] = "4";
		input[7] = "1";
		try {
			output = client.serverCapabilities(input);
		} catch (InvalidSyntaxException e) {
			System.out.println(e.getMessage());
		}
		System.out.println(output);
		
		//Test sendCoordinates
		System.out.println("\n- Test returning the String representation "
				+ "of the coordinates of a move: 2 3\n");
		TowerCoordinates coord = new TowerCoordinates(2, 3);
		System.out.println(client.sendCoordinates(coord));
		
		//Test makeBoard 
		System.out.println("\n- Test making a board by a string of dimensions");
		try {
			Board board = client.makeBoard("4|5|6|3");
			System.out.println("This board was created:\n"
					+ " - x dimension = " + board.xDim + "\n - y dimension = " + board.yDim 
					+ "\n - z dimension = " + board.zDim + "\n - winning length = " 
					+ board.winningLength);
			board = client.makeBoard("4|5|6");
		} catch (InvalidSyntaxException | IllegalBoardConstructorArgumentsException 
				| NumberFormatException e) {
			System.out.println(e.getMessage());
		}
		
		//Test makePlayers
		System.out.println("\n- Test making a List of players by a string of player details");
		String[] validPlayer = new String[3];
		//valid Players
		validPlayer[0] = "2|Aba|342";
		validPlayer[1] = "3|BCb|345";
		validPlayer[2] = "4|Cdc|324";
		try {
			List<Player> players = client.makePlayers(validPlayer);
			System.out.println("These players were created:\n" 
					+ "- amount = " + players.size());
			for (int i = 0; i < players.size(); i++) {
				System.out.println("Player " + i + ": " + players.get(i).name + " with ID = " 
						+ players.get(i).playerID);
			}
					
		} catch (InvalidSyntaxException | NumberFormatException e) {
			System.out.println(e.getMessage());
		}
		//invalid Players
		String[] invalidPlayer = new String[3];
		invalidPlayer[1] = "r|3|7";
		invalidPlayer[2] = "4|dew|3";
		invalidPlayer[0] = "2 23 3";
		try {
			List<Player> players = client.makePlayers(invalidPlayer);
			System.out.println("These players were created:\n" 
					+ "- amount = " + players.size());
			for (int i = 0; i < players.size(); i++) {
				System.out.println("Player " + i + ": " + players.get(i).name + " with ID = " 
						+ players.get(i).playerID);
			}
					
		} catch (InvalidSyntaxException | NumberFormatException e) {
			System.out.println(e.getMessage());
		}
		
		//Test give Boolean
		System.out.println("\nTest the give Boolean method: 0 = no, 1= yes");
		try {
			System.out.println("0: " + client.giveBoolean("0"));
			System.out.println("1: " + client.giveBoolean("1"));
			System.out.println("23: " + client.giveBoolean("23"));
		} catch (InvalidSyntaxException e) {
			System.out.println(e.getMessage());
		}
		
		//Test determine End
		System.out.println("\nTest determine the game's end.");
		System.out.println(client.determineEnd(1, 1));
		System.out.println(client.determineEnd(2, 1));
		System.out.println(client.determineEnd(3, 1));
		System.out.println(client.determineEnd(4, 1));
		System.out.println(client.determineEnd(1));
		System.out.println(client.determineEnd(2));
		System.out.println(client.determineEnd(3));
		System.out.println(client.determineEnd(4));
		System.out.println(client.determineEnd(5));
		
		//Test determineMove
		System.out.println("\nTest determine Move\n - with human Player:");
		client.makeMe("Test", null, 1);
		TowerCoordinates coords = client.determineMove();
		System.out.println("Coordinates of this form: " + coords);
		System.out.println("\n - with Computer player:");
		client.makeMe(null, new RandomStrategy(), 1);
		coords = client.determineMove();
		System.out.println("Coordinates of this form: " + coords);
		
		
		//Test splitString
		// client.react("startGame 3|4|4|4 2|Frank|342 3|kevin|345");
	}
}
