package controller;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.Observable;

import view.ServerTUI;

public class ServerPeer extends Observable {
	private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;
	private ServerTUI view;
	
	public ServerPeer(Socket socket, ServerTUI view) throws IOException {
		this.socket = socket;
		this.view = view;
		in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
	}
	
	public void sendMessage(String message) throws IOException {
		out.write(message);
		out.newLine();
		out.flush();
		view.printMessage(message);
	}
	
	public void run() {
		while (!exit) {
			String message = in.readLine();
			
	}
	
	public void shutdown() {
		
	}
}
