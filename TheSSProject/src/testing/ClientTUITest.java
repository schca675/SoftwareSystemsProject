package testing;

import java.util.ArrayList;
import java.util.List;

import client.Client;
import client.ClientCommunication;
import exc.IllegalBoardConstructorArgumentsException;
import exc.InvalidSyntaxException;
import model.TowerCoordinates;
import view.ClientTUI;
import view.MessageType;

public class ClientTUITest {

	
	public static void main(String[] args) {
		Client client = new Client();
		ClientTUI view = new ClientTUI();
		ClientCommunication comu = new ClientCommunication(view, "Test");
		view.addObserver(comu); 
		comu.makeMe("Test", null, 1);
		try {
			comu.makeBoard("4|4|4|4");
		} catch (InvalidSyntaxException | IllegalBoardConstructorArgumentsException
				| NumberFormatException e) {
			System.out.println(e.getMessage());
		}
		
		// Representation tests (printBoard), also tests drawLine and dashedLine methods
		System.out.println("Testing the representation:\n");
		System.out.println("First test:\n");
		List<List<Integer>> display1 = createFullBoardData(4, 4, 4, 4);
		view.printBoard(display1, 4, 4, 4, 4);
		System.out.println("\n\nSecond test:\n");
		List<List<Integer>> display2 = createNotFullBoardData(3, 4, 4, 2456);
		view.printBoard(display2, 3, 4, 4, 2456);
		System.out.println("\n\nThird test:\n");
		List<List<Integer>> display3 = createNotFullBoardData(5, 7, 10, 4);
		view.printBoard(display3, 5, 7, 10, 4);
		System.out.println("\n\nFourth test:\n");
		List<List<Integer>> display4 = createFullBoardData(1, 1, 1, 4);
		view.printBoard(display4, 1, 1, 1, 4);
		
		//Representation of the board model
		System.out.println("\nRepresentation of the model:\n");
		System.out.println("Board with dimensions x = 4, y = 4:\n");
		view.printModel(4, 4);
		System.out.println("Board with dimensions x = 5, y = 3:\n");
		view.printModel(5, 3);
		System.out.println("Board with dimensions x = 3, y = 5:\n");
		view.printModel(3, 5);
		System.out.println("Board with dimensions x = 10, y = 4:\n");
		view.printModel(10, 4);
		System.out.println("Board with dimensions x = 15, y = 30:\n");
		view.printModel(15, 30);
		
		
		//Test printMessage
		System.out.println("\nTesting the print method:\n Should print: Hello");
		view.print("Hello");
		
		//Test determine Move
		System.out.println("\nTesting determine move\n(without testing "
				+ "if it is valid input on a board):\nTest with:"
				+ " calling Hint, giving invalid input, then valid input\n");
		TowerCoordinates coord = view.determineMove();
		System.out.println("These coordinates are chosen: " + coord.toString());
		coord = view.determineMove();
		System.out.println("These coordinates are chosen: " + coord.toString());

		//Test getString and the print method
		String input = view.getString("\nTesting the getString and print method, "
				+ "should print your input again");
		view.print(input);
		
		//Test readBoolean method
		System.out.println("\nTesting reading boolean method three times");
		boolean bool = view.readBoolean("\nDo you want to do this?", "yes", "no");
		System.out.println(bool);
		bool = view.readBoolean("\nDo you want to do this?", "y", "n");
		System.out.println(bool);
		bool = view.readBoolean("\nDo you want to do this?", "y", "n");
		System.out.println(bool);
		
		//Test print methods
		System.out.println("\nTesting the print methods\n");
		view.valid(MessageType.SOCKET_CREATED);
		view.valid(MessageType.GOT_SERVER_CAP);
		view.valid(MessageType.SENT_CLIENT_CAP);
		view.valid(MessageType.GOT_ID);
		view.valid(MessageType.GAME_START);
		view.valid(MessageType.MOVE_MADE);
		view.errorMessage(MessageType.INVALID_ADDRESS);
		view.errorMessage(MessageType.INVALID_PORT);
		view.errorMessage(MessageType.PROBLEM_DISCONNECTING);
		view.errorMessage(MessageType.INVALID_COORDINATES);
		view.errorMessage(MessageType.INVALID_INPUT);
		view.errorMessage(MessageType.INVALID_STRATEGY);
		view.errorMessage(MessageType.STREAM_FAILURE);
		view.errorMessage(MessageType.WRITING_FAILURE);
		view.errorMessage(MessageType.RETURN_START);
		view.errorMessage(MessageType.SERVER_LISTENING);
		view.errorMessage(MessageType.PROTOCOL_IRREGULARITIES);
		view.errorMessage(MessageType.SERVER_ILLEGAL_MOVE);
		view.errorMessage(MessageType.RETURN_START);
		view.errorMessage(MessageType.SOCKET_FAILURE);

		
		//To test the start menu of the Client we invoke the Client's start menu.
		System.out.println("Test the interaction with the Client controller Class:\n");
		client.start();
	}
	
	/**
	 * Creates board data to test the representation. All the places on the board are occupied.
	 * @param x X dimension
	 * @param y Y dimension
	 * @param z Z dimension
	 * @param id ID the data should be filled with
	 * @return a list of new Board data.
	 */
	public static List<List<Integer>> createFullBoardData(int x, int y, int z, int id) {
		List<List<Integer>> display = new ArrayList<List<Integer>>(16);
		for (int i = 0; i < (x * y); i++) {
			List<Integer> tower = new ArrayList<Integer>();
			for (int j = 0; j < z; j++) {
				tower.add(id);
			}
			display.add(tower);
		}
		return display;
	}
	
	/**
	 * Creates board data to test the representation. Not all the places on the board are occupied.
	 * For every tower there is still one place left.
	 * @param x X dimension
	 * @param y Y dimension
	 * @param z Z dimension
	 * @param id ID the data should be filled with
	 * @return a list of new Board data.
	 */
	public static List<List<Integer>> createNotFullBoardData(int x, int y, int z, int id) {
		List<List<Integer>> display = new ArrayList<List<Integer>>(16);
		for (int i = 0; i < (x * y); i++) {
			List<Integer> tower = new ArrayList<Integer>();
			for (int j = 0; j < z - 1; j++) {
				tower.add(id);
			}
			display.add(tower);
		}
		return display;
	}
}
