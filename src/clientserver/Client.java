package clientserver;

import game.Board;
import game.Disc;
import game.HumanPlayer;
import game.Player;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * Client program for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class Client {
	// The protocol, as discussed in our TI-2 group. For further explanation,
	// you can look at the protocol documentation.
	public static final String CONNECT = "CONNECT";
	public static final String QUIT = "QUIT";
	public static final String INVITE = "INVITE";
	public static final String ACCEPT_INVITE = "ACCEPT";
	public static final String DECLINE_INVITE = "DECLINE";
	public static final String MOVE = "MOVE";
	public static final String CHAT = "CHAT";
	public static final String REQUEST_BOARD = "REQUEST";
	public static final String REQUEST_LOBBY = "LOBBY";
	public static final String REQUEST_LEADERBOARD = "LEADERBOARD";
	public String firstPlayer;
	public String secondPlayer;
	// END OF PROTOCOL

	/**
	 * The name of this Client.
	 */
	private String clientName;

	//TODO: Make this ClientView compatable
	/**
	 * The User Interface of this Client.
	 */
	private ClientTUI mui;
	/**
	 * The Socket of this Client.
	 */
	private Socket sock;
	/**
	 * The BufferedReader that will be used to communicate over the Socket.
	 */
	private BufferedReader in;
	/**
	 * The BufferedWriter that will be used to communicate over the Socket.
	 */
	private BufferedWriter out;
	/**
	 * While this boolean is true, it makes sure that commands are continuously
	 * read from the BufferedReader.
	 */
	private boolean loop;
	/**
	 * A variable to test if a Player is in-game. If they are, they won't
	 * receive any invite messages.
	 */
	private boolean isIngame;
	/**
	 * The Board this Client uses for determining their move.
	 */
	private Board board;
	/**
	 * An integer to determine which Player's turn it is.
	 */
	private String currPlayer;
	private boolean isConnected;
	private Player localPlayer;
	private boolean requestedBoard;
	private Map<String, Integer[]> invitedBy;
	private Map<String, Integer[]> invited;

	/*@	private invariant sock != null;
	 	private invariant mui != null;
	 	private invariant in != null;
	 	private invariant out != null;
	  	private invariant invites != null;
	 */

	/**
	 * Constructs a Client object and tries to make a Socket connection
	 * 
	 * @param name
	 *            The name of this Client object.
	 * @param host
	 *            The IP-adress of this Client
	 * @param port
	 *            The port of this Client
	 * @param muiArg
	 *            The MessageUI for this Client
	 */
	/*@ requires host != null;
	 	requires port >= 1 & port <= 65535;
	 	requires muiArg != null;
	 */
	public Client(InetAddress host, int port, ClientTUI muiArg)
			throws IOException {
		this.sock = new Socket(host, port);
		this.mui = muiArg;
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.loop = true;
		this.isIngame = false;
		this.invitedBy = new HashMap<String, Integer[]>();
		this.isConnected = false;
		//TODO: Needs to be any player.
		this.localPlayer = new HumanPlayer(getClientName(), Disc.YELLOW, muiArg);
		this.requestedBoard = false;
		this.invited = new HashMap<String, Integer[]>();
	}

	/**
	 * This method reads the messages in the InputStream. Then, it decides which
	 * command was sent, and executes this command by calling the method created
	 * for it.
	 */
	public void readInput() {
		while (loop) {
			String line = "";
			try {
				line = in.readLine();
			} catch (IOException | NullPointerException e) {
				shutdown();
			}
			mui.addMessage("Server: " + line);
			String[] serverMessage = line.split("\\s+");
			switch (serverMessage[0]) {
			case Server.ACCEPT_CONNECT:
				isConnected = true;
				connect(serverMessage);
				mui.start();
				break;
			case Server.LOBBY:
				lobby(serverMessage);
				break;
			case Server.INVITE:
				invite(serverMessage);
				break;
			case Server.GAME_START:
				gameStart(serverMessage);
				break;
			case Server.GAME_END:
				gameEnd(serverMessage);
				break;
			case Server.REQUEST_MOVE:
				requestMove(serverMessage);
				break;
			case Server.MOVE_OK:
				moveOK(serverMessage);
				break;
			case Server.ERROR:
				mui.addMessage(line);
				if (!isConnected) {
					mui.askName();
				}
				break;
			case Server.BOARD:
				board = toBoard(line);
				notifyAll();
			}

		}
	}

	/**
	 * This method accepts the Server.CONNECT packet sent by the Server. When
	 * this method is called, it prints that a connection has been established
	 * with the Server, as well as the IP adress and port of the Server. After
	 * this, it lists the features the Server has.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@	requires serverMessage[0].equals(Server.ACCEPT_CONNECT);
	private void connect(String[] serverMessage) {
		mui.addMessage("Successfully established connection to server: "
				+ sock.getRemoteSocketAddress().toString() // IP of
															// the
															// server
				+ ":" + sock.getPort()); // Port of the server
		mui.addMessage("The features of this server are:"
				+ arrayToLine(serverMessage));
	}

	/**
	 * This method accepts the Server.LOBBY packet sent by the Server. When this
	 * method is called, it shows the Client the other Clients that are
	 * currently in the lobby.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.LOBBY);
	private void lobby(String[] serverMessage) {
		mui.addMessage("The people that are currently in the lobby are:"
				+ arrayToLine(serverMessage));
	}

	/**
	 * This method accepts the Server.INVITE packet sent by the Server. When
	 * this method is called, it adds the inviter to an inviterlist, and, if the
	 * player isn't ingame, it will also show the Client that they have been
	 * invited by that Client.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.INVITE);
	private void invite(String[] serverMessage) {
		String opponentName = serverMessage[1];
		if (serverMessage.length == 2) {
			invitedBy.put(opponentName, new Integer[] { 6, 7 });
			if (!isIngame) {
				mui.addMessage("Player: "
						+ opponentName
						+ " has invited you to a game of Connect4 (default boardsize)!");
			}
		} else if (serverMessage.length >= 4) {
			try {
				invitedBy.put(opponentName,
						new Integer[] { Integer.parseInt(serverMessage[2]),
								Integer.parseInt(serverMessage[3]) });
			} catch (NumberFormatException e) {
				mui.addMessage("The server just sent an invite with an invalid custom board size.");
			}
		}
	}

	/**
	 * This method accepts the Server.GAME_START packet sent by the Server. When
	 * this method is called, it will show the Client that a the game is
	 * started. The Client is set to being in-game, and a new Board is created.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@ requires serverMessage[0].equals(Server.GAME_START);
	 	ensures board != null;
	 	ensures this.isIngame;
	 	ensures currPlayer == -1;
	 */
	private void gameStart(String[] serverMessage) {
		firstPlayer = serverMessage[1];
		secondPlayer = serverMessage[2];

		if (firstPlayer.equals(getClientName())) {
			mui.addMessage("A game between you and " + secondPlayer
					+ " has started!");
			Integer[] boardSize = invitedBy.get(secondPlayer);
			if (boardSize != null) {
				board = new Board(boardSize[0], boardSize[1]);
			} else {
				mui.addMessage("Using default boardsize.");
				board = new Board();
			}
		} else {
			mui.addMessage("A game between you and " + firstPlayer
					+ " has started!");
			Integer[] boardSize = invited.get(firstPlayer);
			if (boardSize != null) {
				board = new Board(boardSize[0], boardSize[1]);
			} else {
				mui.addMessage("Using default boardsize.");
				board = new Board();
			}
		}

		this.isIngame = true;
		currPlayer = null; // Not set yet.
		// DEFINITION: currPlayer == 0 > Disc.YELLOW, currPlayer ==
		// 1 > Disc.RED
		// TODO: board size

		invitedBy.clear();
		invited.clear();
		mui.addMessage(board.toString());
		mui.addMessage("You are YELLOW");
	}

	/**
	 * This method accepts the Server.GAME_END packet sent by the Server. When
	 * this method is called, it will set the Client to no longer being in-game.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@	requires serverMessage[0].equals(Server.GAME_END);
	 	ensures !this.isIngame;
	 */
	private void gameEnd(String[] serverMessage) {
		this.isIngame = false;
		if (serverMessage.length > 2) {
			mui.addMessage("The winner is: " + serverMessage[2]);
		} else if (serverMessage.length == 2) {
			if (serverMessage[1].equals(Game.DRAW)) {
				mui.addMessage("The game was a draw!");
			} else {
				mui.addMessage(serverMessage.toString());
			}
		}
	}

	/**
	 * This method accepts the Server.MOVE packet sent by the Server. When this
	 * method is called, it will request a move from the Player.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.REQUEST_MOVE);
	private void requestMove(String[] serverMessage) {
		if (currPlayer == null) {
			currPlayer = firstPlayer;
		}
		localPlayer.determineMove(board);
	}

	/**
	 * This method accepts the Server.MOVE_OK packet sent by the Server. When
	 * this method is called, it will update the Board by inserting the Disc for
	 * the Player that was given in the packet.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.MOVE_OK);
	private synchronized void moveOK(String[] serverMessage) {
		if (currPlayer == null) {
			currPlayer = secondPlayer;
		}
		int move = -1;
		// TODO: betere error handing met request bord
		// TODO: board printen op clientTUI
		if (currPlayer.equals(firstPlayer)) {
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("Server did not send a valid move. TERMINATING.");
				shutdown();
			}
			if (board.isField(move) && board.isEmptyField(move)) {
				board.insertDisc(move, Disc.YELLOW);
				currPlayer = secondPlayer;
			} else {
				if (!requestedBoard) {
					requestBoard();
					requestedBoard = true;
					try {
						wait();
						moveOK(serverMessage);
					} catch (InterruptedException e) {
						mui.addMessage("Interrupted.");
						shutdown();
					}
				} else {
					mui.addMessage("Can't make the move on both the local board, and the board on the server. TERMINATING.");
					shutdown();
				}
			}

		} else if (currPlayer.equals(secondPlayer)) {
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("Server did not send a valid move. TERMINATING.");
				shutdown();
			}
			if (board.isField(move) && board.isEmptyField(move)) {
				board.insertDisc(move, Disc.RED);
				currPlayer = firstPlayer;
			} else {
				if (!requestedBoard) {
					requestBoard();
					requestedBoard = true;
					try {
						wait();
						moveOK(serverMessage);
					} catch (InterruptedException e) {
						mui.addMessage("Interrupted.");
						shutdown();
					}
				} else {
					mui.addMessage("Can't make the move on both the local board, and the board on the server. TERMINATING.");
					shutdown();
				}

				mui.addMessage("Server sent an invalid move. TERMINATING.");
			}
		}
		mui.addMessage(board.toString());
	}

	/**
	 * This method sends a message to the ClientHandler using the OutputStream
	 * out.
	 * 
	 * @param msg
	 *            The message to be sent.
	 */
	//@ requires msg != null;
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	/**
	 * This method closes the Socket connection and exits the program. On a side
	 * note, before it does this, it also sets the loop and isIngame variables
	 * for this Client to false.
	 */
	/*@	ensures !loop;
	 	ensures !isIngame;
	 */
	public void shutdown() {
		loop = false;
		isIngame = false;
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * This method returns the name of this Client.
	 */
	/*@ pure */public String getClientName() {
		return clientName;
	}

	public void setClientName(String name) {
		clientName = name;
	}

	//@ requires line != null;
	public Board toBoard(String line) {
		String[] protocol = line.split(" ");
		Board test = null;
		try {
			int boardColumns = Integer.parseInt(protocol[1]);
			int boardRows = Integer.parseInt(protocol[2]);
		
		test = new Board(boardRows, boardColumns);
		int i = 3;
		for (int row = boardRows - 1; row >= 0; row--) {
			for (int col = 0; col < boardColumns; col++) {
				if (Integer.parseInt(protocol[i]) == 0) {
					//Disc.EMPTY
					test.setField(row, col, Disc.EMPTY);
				} else if (Integer.parseInt(protocol[i]) == 1) {
					//Disc.YELLOW
					test.setField(row, col, Disc.YELLOW);
				} else if (Integer.parseInt(protocol[i]) == 2) {
					//Disc.RED
					test.setField(row, col, Disc.RED);
				}
				i++;
			}
		}
		
		} catch (NumberFormatException e) {
			mui.addMessage("Server sent a wrong board. TERMINATING.");
			shutdown();
		}
		return test;
	}

	//@ requires array != null;
	public String arrayToLine(String[] array) {
		String retLine = "";
		for (int i = 1; i < array.length; i++) {
			retLine += " " + array[i];
		}
		return retLine;
	}

	private void requestBoard() {
		sendMessage(REQUEST_BOARD);
	}

	public void addInvite(String name) {
		addInvite(name, 6, 7);
	}

	public void addInvite(String name, int BoardX, int BoardY) {
		invited.put(name, new Integer[] { BoardX, BoardY });
	}
} // end of class Client
