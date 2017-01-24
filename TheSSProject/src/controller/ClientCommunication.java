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
import model.Player;
import view.ClientTUI;

public class ClientCommunication extends Thread {
	private Player me;
	private ComputerPlayer hintGiver;
	private List<Player> players;
	private Board board;
	
	private ClientTUI view;
	
	// <<---- Variables needed for communication --------->>
	private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;
	
	/**
	 * Creates a new Client Communcation thread.
	 * @param socket Socket the thread should listen to.
	 * @param view TUI of the client.
	 * @throws IOException in case the streams can not be initialized.
	 */
	public ClientCommunication(Socket socket, ClientTUI view) throws IOException {
		this.view = view;
		this.socket = socket;
		in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
	}
	
	/**
	 * Starts the ClientCommunication thread.
	 */
	public void run() {
		
	}
	
	/**
	 * Listens to the incoming messages of the InputStream.
	 */
	public String listen() {
		return null;
	}
	
	/**
	 * Reacts to the incoming messages by the protocol and calls the corresponding methods.
	 */
	public void react(String message)  {
		
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
	
}
