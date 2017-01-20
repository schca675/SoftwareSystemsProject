package controller;

import java.io.BufferedReader;
import java.io.BufferedWriter;
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
	
	public ServerPeer(Socket socket, ServerTUI view) {
		this.socket = socket;
/*		in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));*/
	}
	
/*	public void run() {
		sendCapabilities();
		while (!exit) {
			
		}
	}*/
}
