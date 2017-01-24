package testing;

import controller.ClientCommunication;
import model.InvalidSyntaxException;

public class ClientCommunicationTest {

	public static void main(String[] args) {
		// Test the send Client capabilities 
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
	}
}
