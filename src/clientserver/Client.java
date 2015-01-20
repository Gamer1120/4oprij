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
import java.util.ArrayList;

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
	public static final int FIRST_PLAYER = 0;
	public static final int SECOND_PLAYER = 1;
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
	 * An ArrayList in which all the invites that are sent by this client are
	 * kept.
	 */
	private ArrayList<String> invites;
	/**
	 * The Board this Client uses for determining their move.
	 */
	private Board board;
	/**
	 * An integer to determine which Player's turn it is.
	 */
	private int currPlayer;
	private boolean isConnected;
	private Player localPlayer;

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
		this.invites = new ArrayList<String>();
		this.isConnected = false;
		//TODO: Needs to be any player.
		this.localPlayer = new HumanPlayer(getClientName(), Disc.YELLOW, muiArg);
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
				connectChecks(serverMessage);
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
				toBoard(line);
			}

		}
	}

	/**
	 * This method checks whether the information in the Server.CONNECT packet
	 * is valid. If the server has features, for each feature is made sure that
	 * the length of that feature isn't over 15 characters. If it passes the
	 * test, or the server has no features, the connect method is called.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	private void connectChecks(String[] serverMessage) {
		// TODO: Check the list of features as specified in the Protocol.
		// If the server has features.
		if (!(serverMessage.length == 1)) {
			// For serverMessage[1] - serverMessage[serverMessage.length - 1]:
			// check that the feature isn't longer than 15 characters.
			boolean validFeatures = true;
			for (int i = 1; i < serverMessage.length; i++) {
				if (serverMessage[i].length() > 15) {
					validFeatures = false;
				}
			}
			if (!validFeatures) {
				mui.addMessage("Server has a feature that has a length of over 15 characters. This is against the protocol. TERMINATING.");
				shutdown();
			} else {
				// Connect to a server with features.
				connect(serverMessage);
			}
		} else {
			// Connect to a server without features.
			connect(serverMessage);
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
	private void connect(String[] serverMessage) {
		mui.addMessage("Successfully established connection to server: "
				+ sock.getRemoteSocketAddress().toString() // IP of
															// the
															// server
				+ ":" + sock.getPort()); // Port of the server
		String listOfFeatures = "";
		for (int i = 1; i < serverMessage.length; i++) {
			listOfFeatures += " " + serverMessage[i];
		}
		mui.addMessage("The features of this server are:" + listOfFeatures);
	}

	/**
	 * This method accepts the Server.LOBBY packet sent by the Server. When this
	 * method is called, it shows the Client the other Clients that are
	 * currently in the lobby.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	private void lobby(String[] serverMessage) {
		String listOfPeople = "";
		for (int i = 1; i < serverMessage.length; i++) {
			listOfPeople += " " + serverMessage[i];
		}
		mui.addMessage("The people that are currently in the lobby are:"
				+ listOfPeople);
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
	private void invite(String[] serverMessage) {
		String opponentName = serverMessage[1];
		invites.add(opponentName);
		if (!isIngame) {
			mui.addMessage("Player: " + opponentName
					+ " has invited you to a game of Connect4!");
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
	private void gameStart(String[] serverMessage) {
		mui.addMessage("A game between you and " + serverMessage[2]
				+ " has started!");
		this.isIngame = true;
		currPlayer = -1; // Not set yet.
		// DEFINITION: currPlayer == 0 > Disc.YELLOW, currPlayer ==
		// 1 > Disc.RED
		// TODO: board size
		board = new Board();
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
	private void gameEnd(String[] serverMessage) {
		this.isIngame = false;
		if (serverMessage.length > 2) {
			mui.addMessage("The winner is: " + serverMessage[2]);
		} else if (serverMessage.length == 2){
			if(serverMessage[1].equals(Game.DRAW)){
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
	private void requestMove(String[] serverMessage) {
		if (currPlayer == -1) {
			currPlayer = FIRST_PLAYER;
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
	private void moveOK(String[] serverMessage) {
		if (currPlayer == -1) {
			currPlayer = SECOND_PLAYER;
		}
		int move = -1;
		// TODO: betere error handing met request bord
		// TODO: board printen op clientTUI
		if (currPlayer == FIRST_PLAYER) {
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("Server did not send a valid move. TERMINATING.");
				shutdown();
			}
			if (board.isField(move) && board.isEmptyField(move)) {
				board.insertDisc(move, Disc.YELLOW);
				currPlayer = SECOND_PLAYER;
			} else {
				//TODO: Add toBoard method
				mui.addMessage("Server sent an invalid move. TERMINATING.");
			}

		} else if (currPlayer == SECOND_PLAYER) {
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("Server did not send a valid move. TERMINATING.");
				shutdown();
			}
			if (board.isField(move) && board.isEmptyField(move)) {
				board.insertDisc(move, Disc.RED);
				currPlayer = FIRST_PLAYER;
			} else {
				//TODO: Add toBoard method
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
	public void shutdown() {
		loop = false;
		isIngame = false;
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.exit(0);
	}

	/**
	 * This method returns the name of this Client.
	 */
	public String getClientName() {
		return clientName;
	}

	public Board toBoard(String line) {
		//TODO: Wait for Matthias to Protocol, then implement this method.
		return null;
	}

} // end of class Client
