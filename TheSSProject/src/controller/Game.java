package controller;

import java.util.Random;

import model.Board;
import model.Player;
import model.PlayerID;

public class Game {
	
	// <------ Constants ------>
	
	public static final int NUMBER_PLAYERS = 2;
	
	// <------ Instance variables ------>
	
	//@ private invariant board != null;
	//@ private invariant players !=null && players.length == NUMBER_PLAYERS;
	//@ private invariant (\forall int i; i >= 0 && i < NUMBER_PLAYERS; players[i] != null);
	//@ private invariant currentPlayerIndex >= 0 && currentPlayerIndex < NUMBER_PLAYERS;
	private Board<PlayerID> board;
	private Player[] players;
	private int currentPlayerIndex;
	
	// <------ Constructors ------>
	
	/**
	 * Create a game with default setting and rules.
	 * 
	 * @param player1 Player 1
	 * @param player2 Player 2
	 */
	//@ requires player1 != null && player2 != null;
	public Game(Player player1, Player player2) {
		board = new Board<PlayerID>();
		players[0] = player1;
		players[1] = player2;
		currentPlayerIndex = randomStarter();	
	}
	
	/**
	 * Creates a game with specified dimensions of the board and winning length.
	 * @param player1 Player 1
	 * @param player2 Player 2
	 * @param xDim X dimension of the board
	 * @param yDim Y dimension of the board
	 * @param zDim Z dimension of the board, -1 specifies unlimited
	 * @param winningLength Connected pieces required to win the game
	 */
	//@ requires player1 != null && player2 != null;
	/*@ requires winningLength <= xDim || winningLength <= yDim 
	  @ || (zDim > 0 && winningLength <= zDim) || (zDim == Board.UNLIMITED_Z);
	*/
	//@ requires xDim > 0 && yDim > 0 && (zDim > 0 || zDim == -1) && winningLength > 0;
	public Game(Player player1, Player player2, int xDim, int yDim, int zDim, int winningLength) {
		board = new Board(xDim, yDim, zDim, winningLength);
		players[0] = player1;
		players[1] = player2;
		currentPlayerIndex = randomStarter();
	}
	
	// <------ Queries ------>
	
	/**
	 * Determines a random starter of the game
	 * @return the index of the starting player
	 */
	//@ ensures \result >= 0 && \result < NUMBER_PLAYERS;
	public int randomStarter() {
		Random random = new Random();
		return random.nextInt(NUMBER_PLAYERS);		
	}
	
	// <------ Commands ------>
}
