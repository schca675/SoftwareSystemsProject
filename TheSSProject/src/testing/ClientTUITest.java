package testing;

import java.util.ArrayList;
import java.util.List;

import client.Client;
import view.ClientTUI;

public class ClientTUITest {

	
	public static void main(String[] args) {
		Client client = new Client();
		ClientTUI view = new ClientTUI(client);
		// Representation tests
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
