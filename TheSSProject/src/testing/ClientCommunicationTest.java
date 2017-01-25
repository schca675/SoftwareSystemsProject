package testing;

import java.util.List;

import controller.ClientCommunication;
import model.Board;
import model.IllegalBoardConstructorArgumentsException;
import model.InvalidSyntaxException;
import model.Player;
import model.TowerCoordinates;

public class ClientCommunicationTest {

	/**
	 * Test the client communication Clas.
	 * @param args does not need any.
	 */
	public static void main(String[] args) {
		// Test the send Client capabilities 
		System.out.println("- Test the send Client's capabilities\n");
		ClientCommunication client = new ClientCommunication("Test");
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
		} catch (InvalidSyntaxException | IllegalBoardConstructorArgumentsException 
				| NumberFormatException e) {
			System.out.println(e.getMessage());
		}
		
		//Test makePlayers
		//TODO does not work yet.
		System.out.println("\n- Test making a List of players by a string of player details");
		String[] inputPlayer = new String[3];
		inputPlayer[0] = "2|Frank|342";
		inputPlayer[1] = "3|kevin|345";
		inputPlayer[2] = "4|cathy|324";
		try {
			List<Player> players = client.makePlayers(inputPlayer);
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
		System.out.println("\nTest determine end, when the game ended.");
		System.out.println(client.determineEnd(1, 1));
		System.out.println(client.determineEnd(2, 1));
		System.out.println(client.determineEnd(3, 1));
		System.out.println(client.determineEnd(4, 1));
		System.out.println(client.determineEnd(1));
		System.out.println(client.determineEnd(2));
		System.out.println(client.determineEnd(3));
		System.out.println(client.determineEnd(4));
		System.out.println(client.determineEnd(5));
		
		//Test splitString
		// client.react("startGame 3|4|4|4 2|Frank|342 3|kevin|345");
	}
}
