package model;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

public class Board<P> {
	
	// <------ Constants ------>
	
	public static final int DEFAULT_XDIM = 4;
	public static final int DEFAULT_YDIM = 4;
	public static final int DEFAULT_ZDIM = 4;
	public static final int DEFAULT_WIN = 4;
	public static final int UNLIMITED_Z = -1;
	
	// <------ Instance variables ------>
	
	// With public final, they are visible but can't be changed after being set.
	// Saves the redundant getters.
	public final int xDim;
	public final int yDim;
	public final int zDim;
	public final int winningLength;
	private List<List<P>> boardData;
	
	// <------ Constructors ------>
	
	/** Create a new board with specified dimensions and winning length.
	 * @param xDim X dimension of the board
	 * @param yDim Y dimension of the board
	 * @param zDim Z dimension of the board, -1 specifies unlimited
	 * @param winningLength Connected pieces required to win the game
	 */
	/*@ requires winningLength <= xDim || winningLength <= yDim 
	  @ 			|| (zDim > 0 && winningLength <= zDim) || (zDim == UNLIMITED_Z);
	 */
	//@ requires xDim > 0 && yDim > 0 && (zDim > 0 || zDim == -1) && winningLength > 0;
	public Board(int xDim, int yDim, int zDim, int winningLength) {
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
		this.winningLength = winningLength;
		reset();
	}
	
	/** Create a board with default settings and rules.
	 * 
	 */
	public Board() {
		this(DEFAULT_XDIM, DEFAULT_YDIM, DEFAULT_ZDIM, DEFAULT_WIN);
	}
	
	
	// <------ Queries ------>	
	
	/** Gets the tower at (x,y), assuming there is one.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return Tower at (x,y)
	 */
	//@ requires isValidTower(x,y);
	/*@ pure */ private List<P> getTower(int x, int y) {
		return boardData.get((x - 1) + (y - 1) * yDim);
	}
	
	/** Checks whether a piece can be added at (x,y).
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @return Tower at (x,y) exists and isn't full
	 */
	//@ ensures zDim == UNLIMITED_Z ==> \result == (isValidTower(x,y));
	//@ ensures zDim > 0 ==> \result == (isValidTower(x,y) && getTowerHeight(x,y) < zDim);
	/*@ pure */ public boolean checkMove(int x, int y) {
		if (zDim == UNLIMITED_Z) {
			return isValidTower(x, y);
		} else {
			return isValidTower(x, y) && getTowerHeight(x, y) < zDim;
		}
	}
	
	/** Returns the owner of the (assumed valid) cell (x,y,z), null if no owner.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return Owner, null if no owner
	 */
	//@ requires isValidCell(x,y,z);
	//TODO: JML refuses generic type P
	// ensures \result == null || \result instanceof P;
	/*@ pure nullable */ public P getCellOwner(int x, int y, int z) {
		if (z <= getTowerHeight(x, y)) {
			return getTower(x, y).get(z - 1);
		} else {
			return null;
		}
	}
	/** Checks whether the given cell is empty.
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @return (x,y,z) is empty
	 */
	//@ requires isValidCell(x,y,z);
	//@ ensures \result == (getCellOwner(x,y,z) == null);
	/*@ pure */ public boolean isEmptyCell(int x, int y, int z) {
		return getCellOwner(x, y, z) == null;
	}
	
	/** Checks whether the board is full.
	 * 
	 * @return Board is full
	 */
	//@ ensures \result == (\forall int x,y,z; isValidCell(x,y,z); !isEmptyCell(x,y,z));
	/*@ pure */ public boolean isFull() {
		if (zDim == UNLIMITED_Z) {
			return false;
		} else {
			for (List<P> tower : boardData) {
				if (tower.size() < zDim) {
					return false;
				}
			}
			return true;
		}
	}
	
	/** Returns the height of the tower at (x,y).
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @return The height of the tower at (x,y)
	 */
	//@ requires isValidTower(x,y);
	//@ ensures \result >= 0 && (\result <= zDim || zDim == UNLIMITED_Z);
	//@ ensures \forall int z; isValidCell(x,y,z); isEmptyCell(x,y,z) == (z > \result);
	/*@ pure */ public int getTowerHeight(int x, int y) {
		return getTower(x, y).size();
	}
	
	/** Checks whether the piece at (x,y,z) belongs to a winning set.
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @return Piece at (x,y,z) belongs to winning set
	 */
	//@ requires isValidCell(x,y,z) && !isEmptyCell(x,y,z);
	//TODO: ensures part?
	/*@ pure */ public boolean hasWon(int x, int y, int z) {
		// Linearly independent direction vectors:
		// (1,0,0) X-direction
		// (0,1,0) Y-direction
		// (0,0,1) Z-direction
		// (1,1,0) X+Y-direction
		// (1,-1,0) X-Y-direction
		// (1,0,1) X+Z-direction
		// (1,0,-1) X-Z-direction
		// (0,1,1) Y+Z-direction
		// (0,1,-1) Y-Z-direction
		// (1,1,1) X+Y+Z-direction
		// (1,1,-1) X+Y-Z-direction
		// (1,-1,1) X-Y+Z-direction
		// (1,-1,-1) X-Y-Z-direction
		return directionHasWon(x, y, z, 1, 0, 0) || 
				directionHasWon(x, y, z, 0, 1, 0) || 
				directionHasWon(x, y, z, 0, 0, 1) || 
				directionHasWon(x, y, z, 1, 1, 0) ||
				directionHasWon(x, y, z, 1, -1, 0) || 
				directionHasWon(x, y, z, 1, 0, 1) ||
				directionHasWon(x, y, z, 1, 0, -1) || 
				directionHasWon(x, y, z, 0, 1, 1) ||
				directionHasWon(x, y, z, 0, 1, -1) || 
				directionHasWon(x, y, z, 1, 1, 1) ||
				directionHasWon(x, y, z, 1, 1, -1) || 
				directionHasWon(x, y, z, 1, -1, 1) ||
				directionHasWon(x, y, z, 1, -1, -1);
	}
	
	/** Checks whether the direction (deltax,deltay,deltaz) 
	 * belonging to the cell (x,y,z) is winning. 
	 * 
	 * @param x X position of cell
	 * @param y Y position of cell
	 * @param z Z position of cell
	 * @param deltax X direction
	 * @param deltay Y direction
	 * @param deltaz Z direction
	 * @return Direction has won
	 */
	//@ requires isValidCell(x,y,z) && !isEmptyCell(x,y,z);
	//TODO: ensures part?
	/*@ pure */ private boolean directionHasWon(int x, int y, int z, 
													int deltax, int deltay, int deltaz) {
		int connectedPieces = 1;
		P owner = getCellOwner(x, y, z);
		int distance = 1;
		int sign = 1;
		while (connectedPieces < winningLength) {
			int checkX = x + sign * distance * deltax;
			int checkY = y + sign * distance * deltay;
			int checkZ = z + sign * distance * deltaz;
			if (isValidCell(checkX, checkY, checkZ) && getCellOwner(checkX, checkY, checkZ) != null
					&& getCellOwner(checkX, checkY, checkZ).equals(owner)) {
				connectedPieces = connectedPieces + 1;
				distance = distance + 1;
			} else {
				if (sign == 1) {
					//Reverse
					sign = -1;
					distance = 1;
				} else {
					//If reversed already, terminate
					return false;
				}
			}
		}
		return true;
	}
	
	/** Checks whether (x,y) is a valid tower on the board.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return (x,y) are valid coordinates on the board
	 */
	//@ ensures \result == (x > 0 && x <= xDim && y > 0 && y <= yDim);
	/*@ pure */ public boolean isValidTower(int x, int y) {
		return x > 0 && x <= xDim && y > 0 && y <= yDim;
	}
	
	/** Checks whether (x,y,z) is a valid cell on the board.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return (x,y,z) are valid coordinates on the board
	 */
	//@ ensures \result == (isValidTower(x,y) && ((z > 0 && z <= zDim) || zDim == UNLIMITED_Z));
	/*@ pure */ public boolean isValidCell(int x, int y, int z) {
		if (zDim == UNLIMITED_Z) {
			return isValidTower(x, y);
		} else {
			return isValidTower(x, y) && z > 0 && z <= zDim;
		}
	}
	
	/** Returns the coordinates belonging to a tower index.
	 * 
	 * @param i index
	 * @return Coordinates of tower
	 */
	//@ requires i >= 0 && i < xDim * yDim - 1;
	//@ ensures isValidTower(\result.getX(),\result.getY());
	/*@ pure */ private Coordinates getTowerCoordinates(int i) {
		int x = i % yDim + 1;
		int y = i / yDim + 1;
		return new Coordinates(x, y);
	}
	
	/** Returns the coordinates of each tower where a piece can be added.
	 * 
	 * @return Available towers
	 */
	/*@ ensures \forall Coordinates coord; \result.contains(coord); 
	  @										checkMove(coord.getX(),coord.getY()); 
	/*@ pure */ public List<Coordinates> getAvailableTowers() {
		ListIterator<List<P>> iterator = boardData.listIterator();
		List<Coordinates> availableTowers = new ArrayList<Coordinates>();
		if (zDim == UNLIMITED_Z) {
			while (iterator.hasNext()) {
				availableTowers.add(getTowerCoordinates(iterator.nextIndex()));
				iterator.next();
			}
		} else {
			while (iterator.hasNext()) {
				int x = getTowerCoordinates(iterator.nextIndex()).getX();
				int y = getTowerCoordinates(iterator.nextIndex()).getY();
				if (getTowerHeight(x, y) < zDim) {
					availableTowers.add(new Coordinates(x, y));
				}
				iterator.next();
			}
		}
		return availableTowers;
	}
	
	/** Creates and returns a deep copy of the board.
	 * 
	 * @return Deep copy of this board
	 */
	//@ ensures \result.equals(this);
	/*@ pure */ public Board<P> deepCopy() {
		Board<P> boardCopy = new Board<P>(xDim, yDim, zDim, winningLength);
		Iterator<List<P>> oldBoardIterator = boardData.iterator(); 
		Iterator<List<P>> newBoardIterator = boardCopy.boardData.iterator(); 
		while (oldBoardIterator.hasNext()) {
			newBoardIterator.next().addAll(oldBoardIterator.next());
		}
		return boardCopy;
	}
	
	
	// <------ Commands ------>
	
	/** Make a move if it is valid.
	 * 
	 * @param x X position to place piece at
	 * @param y Y position to place piece at
	 * @param playerID ID of player that makes a move
	 * @return Move successful
	 */
	/*@ ensures \old(checkMove(x,y)) ==> \result == true;
	  @ ensures \result == true ==> getCellOwner(x,y,getTowerHeight(x,y)) == playerID && 
	  @ 								getTowerHeight(x,y) == \old(getTowerHeight(x,y)) + 1;
	 */
	public boolean makeMove(int x, int y, P playerID) {
		if (checkMove(x, y)) {
			getTower(x, y).add(playerID);
			return true;
		} else {
			return false;
		}
	}
	
	/** Resets the board to an empty board.
	 * 
	 */
	//@ ensures \forall int x,y,z; isValidCell(x,y,z); isEmptyCell(x,y,z);
	public void reset() {
		boardData = new ArrayList<List<P>>(xDim * yDim);
		// More efficient way to do this?
		for (int i = 0; i < xDim * yDim; i++) {
			boardData.add(new ArrayList<P>());
		}
	}
}
