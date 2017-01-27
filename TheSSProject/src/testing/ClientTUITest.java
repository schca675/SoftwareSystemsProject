package testing;

import java.util.ArrayList;
import java.util.List;

import client.Client;
import client.ClientCommunication;
import exc.IllegalBoardConstructorArgumentsException;
import exc.InvalidSyntaxException;
import model.MessageType;
import model.TowerCoordinates;
import view.ClientTUI;

public class ClientTUITest {

	
	public static void main(String[] args) {
		//TODO Exit?
		Client client = new Client();
		ClientTUI view = new ClientTUI(client);
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
		List<List<Integer>> display1 = createBoardData(4, 4, 4, 4);
		view.printBoard(display1, 4, 4, 4, 4);
		System.out.println("\n\nSecond test:\n");
		List<List<Integer>> display2 = createBoardData(3, 4, 4, 2456);
		view.printBoard(display2, 3, 4, 4, 2456);
		System.out.println("\n\nThird test:\n");
		List<List<Integer>> display3 = createBoardData(5, 7, 10, 4);
		view.printBoard(display3, 5, 7, 10, 4);
		System.out.println("\n\nFourth test:\n");
		List<List<Integer>> display4 = createBoardData(1, 1, 1, 4);
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
		System.out.println("\nTesting determine move four times\n(without testing "
				+ "if it is valid input on a board):\n1) input is correct (Integer Integer)");
		TowerCoordinates coord = view.determineMove();
		System.out.println("These coordinates are chosen: " + coord.toString());
		System.out.println("\n2) with Hint chosen"); 
		coord = view.determineMove();
		System.out.println("These coordinates are chosen: " + coord.toString());
		System.out.println("\n3) with Hint not chosen and regular input"); 
		coord = view.determineMove();
		System.out.println("These coordinates are chosen: " + coord.toString());
		System.out.println("\n4) with giving a invalid input"); 
		coord = view.determineMove();
		System.out.println("These coordinates are chosen: " + coord.toString());
	
		//Test getString method
		String input = view.getString("\nTesting the getString method, "
				+ "should print your input again");
		System.out.println(input);
		
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
		view.errorMessage(MessageType.INVALID_ADDRESS);
		view.errorMessage(MessageType.INVALID_PORT);
		view.errorMessage(MessageType.PROBLEM_DISCONNECTING);
		view.errorMessage(MessageType.INVALID_COORDINATES);
		view.errorMessage(MessageType.SOCKET_FAILURE);
		view.errorMessage(MessageType.INVALID_INPUT);
		view.errorMessage(MessageType.INVALID_STRATEGY);
		view.errorMessage(MessageType.STREAM_FAILURE);
		view.errorMessage(MessageType.WRITING_FAILURE);
		view.errorMessage(MessageType.RETURN_START);
		view.errorMessage(MessageType.SERVER_LISTENING);
		view.errorMessage(MessageType.PROTOCOL_IRREGULARITIES);
		view.errorMessage(MessageType.SERVER_ILLEGAL_MOVE);
		
		//Test start: StartMenu should show up and answer questions until the socket connection.
		// So to test: Help menu, Exit, Play: Com and Human, Def and Own.
		System.out.println("\nTesting the startup:\n");
		//returns to start menu
		view.errorMessage(MessageType.RETURN_START);
		try {
			view.start();
		} catch (NullPointerException e) {
			System.out.println("throws an exception, because the client does "
					+ "not have a socket to close.");
		}
	}
	
	public static List<List<Integer>> createBoardData(int x, int y, int z, int id) {
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
}
