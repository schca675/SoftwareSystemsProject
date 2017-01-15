package controller;

import java.net.InetAddress;
import java.net.Socket;
import java.util.List;
import java.util.Observable;

import model.Board;
import model.Player;
import model.TowerCoordinates;

public class Client extends Observable {
	//Observable if not implemented in Board
	
	private Board board;
	private Socket socket;
	private Player me;
	private List<Player> players;
	
	/**
	 * Constructor, empty for now.
	 */
	public Client() {
		
	}
	
	/**
	 * Connects to the server at given adress.
	 * @param adress
	 */
	public void connectToServer(InetAddress adress) {
		
	}
	
	/**
	 * Creates a new TUI and starts it.
	 * @param args
	 */
	public static void main(String[] args) {
		
	}
	
	/**
	 * Reads a server message from the socket, and calls appropriate methods.
	 */
	public void readServerMessage() {
		
	}
	
	/**
	 * Sends a message to the server via the socket.
	 * @param message
	 */
	public void sendServerMessage(String message) {
		
	}
	
	/** 
	 * Makes the moves on the board, handles boards exception after getting the coordinates from 
	 * the server.
	 * @param x
	 * @param y
	 */
	public void makeMove(int x, int y) {
		
	}
	
	/** 
	 * Determines the next move to play, asks TUI in case of Human Player or the method of Computer
	 * Player, handles exceptions before server communication (local check).
	 * @param x
	 * @param y
	 * @return
	 */
	public TowerCoordinates determineMove(int x, int y) {
		return null;
	}
	
	/** 
	 * Gets the board data from the board for use by the UI.
	 * @return
	 */
	public List<List<Integer>> getBoardData() {
		return null;
	}
	
	/**
	 * Makes the connection to server, calls readTUIMessage(), if rules are fine setup game, 
	 * else notify TUI.
	 * @param message
	 */
	public void startGame(String message) {
		
	}
	
	/**
	 * Reads the message, calls appropriate methods.
	 * @param message
	 */
	public void readTUIMessage(String message) {
		
	}
}
