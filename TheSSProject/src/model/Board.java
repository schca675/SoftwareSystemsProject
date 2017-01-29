package model;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Observable;

import exc.CoordinatesOutOfBoundsException;
import exc.IllegalBoardConstructorArgumentsException;
import exc.IllegalBoardDimensionsException;
import exc.IllegalCoordinatesException;
import exc.IllegalWinningLengthException;
import exc.TowerAlreadyFullException;

public class Board extends Observable {
	
	// <------ Constants ------>
	
	public static final int DEFAULT_DIM = 4;
	public static final int DEFAULT_WIN = 4;
	public static final int UNLIMITED_Z = 0;
	
	// <------ INSTANCE VARIABLES ------>
	
	public final int xDim;
	public final int yDim;
	public final int zDim;
	public final int winningLength;
	private List<List<Integer>> boardData; 
	
	
	// <------ CONSTRUCTORS ------>
	
	/** 
	 * Create a new board with specified dimensions and winning length.
	 * @param xDim X dimension of the board
	 * @param yDim Y dimension of the board
	 * @param zDim Z dimension of the board, -1 specifies unlimited
	 * @param winningLength Connected pieces required to win the game
	 */
	/*@ requires winningLength <= xDim || winningLength <= yDim 
	   				|| (zDim > 0 && winningLength <= zDim) || (zDim == UNLIMITED_Z);
	  @*/
	//@ requires xDim > 0 && yDim > 0 && (zDim > 0 || zDim == UNLIMITED_Z) && winningLength > 0;
	public Board(int xDim, int yDim, int zDim, int winningLength) 
			throws IllegalBoardConstructorArgumentsException {
		if (xDim <= 0 || yDim <= 0 || (zDim <= 0 && zDim != UNLIMITED_Z) || winningLength <= 0) {
			throw new IllegalBoardDimensionsException(xDim, yDim, zDim);
		} else if (winningLength > xDim && winningLength > yDim 
	   			&& (zDim > 0 && winningLength <= zDim)) {
			throw new IllegalWinningLengthException(xDim, yDim, zDim, winningLength);
		}
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
		this.winningLength = winningLength;
		reset();
	}
	
	/** 
	 * Create a board with default settings and rules.
	 */
	public Board() {
		this.xDim = DEFAULT_DIM;
		this.yDim = DEFAULT_DIM;
		this.zDim = DEFAULT_DIM;
		this.winningLength = DEFAULT_WIN;
		reset();
	}
	
	
	// <------ QUERIES ------>	
	
	// <------ Argument validity checks ------>
	
	/** 
	 * Checks whether a piece can be added at (<code>x</code>, <code>y</code>), i.e. if 
	 * (<code>x</code>, <code>y</code>) are	within the board dimensions (<code>xDim</code>, 
	 * <code>yDim</code>) and if the tower height is less than <code>zDim</code>.
	 * @param x X position
	 * @param y Y position
	 * @return Tower at (<code>x</code>, <code>y</code>) exists and isn't full
	 */
	//@ ensures zDim == UNLIMITED_Z ==> \result == (isValidTower(x,y));
	//@ ensures zDim > 0 ==> \result == (isValidTower(x,y) && getTowerHeight(x,y) < zDim);
	/*@ pure @*/ public boolean isValidMove(int x, int y) {
		if (zDim == UNLIMITED_Z) {
			return isValidTower(x, y);
		} else {
			try {
				if (isValidTower(x, y) && getTowerHeight(x, y) < zDim) {
					return true;	
				} else {
					return false;
				}
			} catch (CoordinatesOutOfBoundsException e) {
				return false;
			}
		}
	}
	
	/** 
	 * Checks whether (<code>x</code>, <code>y</code>) is a valid tower on the board, i.e. whether
	 * the tower coordinates are within the board dimensions.
	 * @param x X position
	 * @param y Y position
	 * @return (<code>x</code>, <code>y</code>) are valid tower coordinates
	 */
	//@ ensures \result == (x > 0 && x <= xDim && y > 0 && y <= yDim);
	/*@ pure @*/ public boolean isValidTower(int x, int y) {
		return x > 0 && x <= xDim && y > 0 && y <= yDim;
	}
	
	/** 
	 * Checks whether (<code>x</code>, <code>y</code>, <code>z</code>) is a valid cell on the 
	 * board, i.e. whether the cell coordinates are within the board dimensions.
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return (<code>x</code>, <code>y</code>, <code>z</code>) are valid cell coordinates
	 */
	//@ ensures \result == (isValidTower(x,y) && ((z > 0 && z <= zDim) || zDim == UNLIMITED_Z));
	/*@ pure @*/ public boolean isValidCell(int x, int y, int z) {
		if (zDim == UNLIMITED_Z) {
			return isValidTower(x, y);
		} else {
			return isValidTower(x, y) && z > 0 && z <= zDim;
		}
	}
	
	// <------ Checking for game ends------>
	
	//Used with this number of arguments by test class only
	/** 
	 * Checks whether the piece at (<code>x</code>, <code>y</code>, <code>z</code>) belongs to a
	 * winning set, i.e. it belongs to a connected set of <code>winningLength</code> pieces 
	 * belonging to its owner.
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return Piece at (<code>x</code>, <code>y</code>, <code>getTowerHeight(z)</code>) belongs to
	 * winning set
	 */
	//@ requires isValidCell(x,y,getTowerHeight(x,y)) && !isEmptyCell(x,y,getTowerHeight(x,y));
	//TODO: ensures part?
	/*@ pure @*/ public boolean hasWon(int x, int y, int z) throws CoordinatesOutOfBoundsException {
		Integer owner = getCellOwner(x, y, z);
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
		return directionHasWon(x, y, z, 1, 0, 0, owner) || 
				directionHasWon(x, y, z, 0, 1, 0, owner) || 
				directionHasWon(x, y, z, 0, 0, 1, owner) || 
				directionHasWon(x, y, z, 1, 1, 0, owner) ||
				directionHasWon(x, y, z, 1, -1, 0, owner) || 
				directionHasWon(x, y, z, 1, 0, 1, owner) ||
				directionHasWon(x, y, z, 1, 0, -1, owner) || 
				directionHasWon(x, y, z, 0, 1, 1, owner) ||
				directionHasWon(x, y, z, 0, 1, -1, owner) || 
				directionHasWon(x, y, z, 1, 1, 1, owner) ||
				directionHasWon(x, y, z, 1, 1, -1, owner) || 
				directionHasWon(x, y, z, 1, -1, 1, owner) ||
				directionHasWon(x, y, z, 1, -1, -1, owner);
	}
	
	/** 
	 * Checks whether the <i>last added</i> piece at (<code>x</code>, <code>y</code>) belongs to a
	 * winning set, i.e. it belongs to a connected set of <code>winningLength</code> pieces 
	 * belonging to its owner.
	 * @param x X position
	 * @param y Y position
	 * @return Piece at (<code>x</code>, <code>y</code>, <code>getTowerHeight(z)</code>) belongs to
	 * winning set
	 */
	//@ requires isValidCell(x,y,getTowerHeight(x,y)) && !isEmptyCell(x,y,getTowerHeight(x,y));
	//TODO: ensures part?
	/*@ pure @*/ public boolean hasWon(int x, int y) throws CoordinatesOutOfBoundsException {
		return hasWon(x, y, getTowerHeight(x, y));
	}
	
	/** 
	 * Checks whether the board is full.
	 * @return Board is full
	 */
	//@ ensures \result == (\forall int x,y,z; isValidCell(x,y,z); !isEmptyCell(x,y,z));
	/*@ pure @*/ public boolean isFull() {
		if (zDim == UNLIMITED_Z) { 
			return false;
		} else {
			for (List<Integer> tower : boardData) {
				if (tower.size() < zDim) {
					return false;
				}
			}
			return true;
		}
	}
	
	// <------ Required for AI ------>
	
	/** 
	 * Returns a <code>List</code> of <code>Coordinates</code> of each tower where a piece can be 
	 * added, i.e. towers with valid coordinates that are not full.
	 * @return <code>List</code> of <code>Coordinates</code> of available towers
	 */
	/*@ ensures \forall TowerCoordinates coord; \result.contains(coord); 
	  												isValidMove(coord.getX(),coord.getY()); 
	  @*/
	/*@ pure @*/ public List<TowerCoordinates> getAvailableTowers() {
		List<TowerCoordinates> availableTowers = new ArrayList<TowerCoordinates>();
		List<List<Integer>> allTowers = deepDataCopy();
		for (int i = 0; i < allTowers.size(); i++) {
			int x = getTowerCoordinates(i).getX();
			int y = getTowerCoordinates(i).getY();
			try {
				if (getTowerHeight(x, y) < zDim) {
					availableTowers.add(new TowerCoordinates(x, y));
				}
			} catch (CoordinatesOutOfBoundsException e) { 
				System.err.println("getAvailableTowers method  broken");
				System.err.println(e.getMessage());
				return null;
			}
		}
		return availableTowers;
	}
	
	/** 
	 * Creates and returns a deep copy of the board.
	 * @return Deep copy of this board
	 */
	//@ ensures \result.equals(this);
	/*@ pure @*/ public Board deepCopy() {
		try {
			Board boardCopy = new Board(xDim, yDim, zDim, winningLength);
			Iterator<List<Integer>> oldBoardIterator = boardData.iterator(); 
			Iterator<List<Integer>> newBoardIterator = boardCopy.boardData.iterator(); 
			while (oldBoardIterator.hasNext()) {
				newBoardIterator.next().addAll(oldBoardIterator.next());
			}
			return boardCopy;
		} catch (IllegalBoardConstructorArgumentsException e) {
			System.err.println("This can't ever happen :S");
			System.err.println(e.getMessage());
			return null;
		}
	}
	
	// <------ Required to present the data to the GUI without using another data format ------>
	
	/** 
	 * Creates and returns a deep copy of the <code>boardData</code>, for use by the view.
	 * @return Copy of the board data.
	 */
	/*@ pure @*/ public List<List<Integer>> deepDataCopy() {
		return deepCopy().boardData;
	}
	
	// <------ Internal workings ------>
	
	// Used externally by test class
	/** 
	 * Returns the owner of the cell (<code>x</code>, <code>y</code>, <code>z</code>), null if no
	 * owner.
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return Owner, null if no owner
	 */
	//@ requires isValidCell(x,y,z);
	//@ ensures \result == null || \result instanceof Integer;
	/*@ pure nullable @*/ public Integer getCellOwner(int x, int y, int z) throws 
					CoordinatesOutOfBoundsException {
		if (z <= getTowerHeight(x, y) && z > 0) {
			return getTower(x, y).get(z - 1);
		} else {
			return null;
		}
	}
	
	// Used externally by test class
	/** 
	 * Checks whether the given cell is empty, i.e. <code>getCellOwner(x, y, z) == null</code>.
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @return (<code>x</code>, <code>y</code>, <code>z</code>) is empty
	 */
	//@ requires isValidCell(x,y,z);
	//@ ensures \result == (getCellOwner(x,y,z) == null);
	/*@ pure @*/ public boolean isEmptyCell(int x, int y, int z) throws 
					CoordinatesOutOfBoundsException {
		return getCellOwner(x, y, z) == null;
	}
	
	// Still needed for current implementation of the controller.
	/** 
	 * Returns the height of the tower at (<code>x</code>, <code>y</code>).
	 * @param x X position
	 * @param y Y position
	 * @return The height of the tower at (<code>x</code>, <code>y</code>)
	 */
	//@ requires isValidTower(x,y);
	//@ ensures \result >= 0 && (\result <= zDim || zDim == UNLIMITED_Z);
	//@ ensures \forall int z; isValidCell(x,y,z); isEmptyCell(x,y,z) == (z > \result);
	/*@ pure @*/ public int getTowerHeight(int x, int y) throws CoordinatesOutOfBoundsException {
		return getTower(x, y).size();
	}
	
	/** 
	 * Gets the tower at (<code>x</code>, <code>y</code>).
	 * @param x X position
	 * @param y Y position
	 * @return Tower at (<code>x</code>, <code>y</code>)
	 */
	//@ requires isValidTower(x,y);
	/*@ pure @*/ public List<Integer> getTower(int x, int y) 
					throws CoordinatesOutOfBoundsException {
		if (!isValidTower(x, y)) {
			throw new CoordinatesOutOfBoundsException(x, y, this);
		}
		return boardData.get((x - 1) + (y - 1) * xDim);
		//TODO changed.
	}
	
	/** 
	 * Checks whether the direction (<code>xDir</code>, <code>yDir</code>, 
	 * <code>zDir</code>), including its reverse, starting at the cell (<code>x</code>, 
	 * <code>y</code>, <code>z</code>) is winning. 
	 * @param x X position of cell
	 * @param y Y position of cell
	 * @param z Z position of cell
	 * @param xDir X direction
	 * @param yDir Y direction
	 * @param zDir Z direction
	 * @return Direction has won
	 */
	//@ requires isValidCell(x,y,z) && !isEmptyCell(x,y,z);
	//TODO: ensures part?
	/*@ pure @*/ private boolean directionHasWon(int x, int y, int z, 
													int xDir, int yDir, int zDir, Integer owner) {
		int connectedPieces = 1;
		int distance = 1;
		int sign = 1;
		while (connectedPieces < winningLength) {
			int checkX = x + sign * distance * xDir;
			int checkY = y + sign * distance * yDir;
			int checkZ = z + sign * distance * zDir;
			try {
				if (isValidCell(checkX, checkY, checkZ) && getCellOwner(checkX, checkY, checkZ) 
						!= null	&& getCellOwner(checkX, checkY, checkZ).equals(owner)) {
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
			} catch (CoordinatesOutOfBoundsException e) {
				System.err.println("directionHasWon method is broken");
				System.err.println(e.getMessage());
				return false;
			}
		}
		return true;
	}
	
	/** 
	 * Returns the <code>TowerCoordinates</code> belonging to a tower index.
	 * @param i index
	 * @return <code>TowerCoordinates</code> of tower
	 */
	//@ requires i >= 0 && i < xDim * yDim - 1;
	//@ ensures isValidTower(\result.getX(),\result.getY());
	/*@ pure @*/ public TowerCoordinates getTowerCoordinates(int i) {
		int x = i % xDim + 1;
		int y = i / xDim + 1;
		return new TowerCoordinates(x, y);
	}
	
	
	// <------ COMMANDS ------>
	
	// <------ What it's all about ------>
	
	/** 
	 * Add a piece to the tower at (<code>x</code>, <code>y</code>).
	 * @param x X position to place piece at
	 * @param y Y position to place piece at
	 * @param playerID ID of player that makes a move
	 */
	//@ requires isValidMove(x,y);
	/*@ ensures getCellOwner(x,y,getTowerHeight(x,y)) == playerID && 
	   			getTowerHeight(x,y) == \old(getTowerHeight(x,y)) + 1;
	  @*/
	public void makeMove(int x, int y, Integer playerID) throws IllegalCoordinatesException {
		if (isValidMove(x, y)) {
			getTower(x, y).add(playerID);
			setChanged();
			notifyObservers(1);
		} else if (!isValidTower(x, y)) {
			throw new CoordinatesOutOfBoundsException(x, y, this);
		} else if (zDim != UNLIMITED_Z && getTowerHeight(x, y) >= zDim) {
			throw new TowerAlreadyFullException(x, y, this);
		}
	}
	
	// <------ Internal workings ------>
	
	/** 
	 * Resets the board to an empty board.
	 */
	//@ ensures \forall int x,y,z; isValidCell(x,y,z); isEmptyCell(x,y,z);
	private void reset() {
		boardData = new ArrayList<List<Integer>>(xDim * yDim);
		if (zDim == UNLIMITED_Z) {
			for (int i = 0; i < xDim * yDim; i++) {
				boardData.add(new ArrayList<Integer>(50));
			}
		} else {
			for (int i = 0; i < xDim * yDim; i++) {
				boardData.add(new ArrayList<Integer>(zDim));
			}
		}
	}
}
